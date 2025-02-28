/**
 * Path-sensitive interprocedural taint analysis for detecting unprotected calls.
 *
 * This detector implements a simplified version to identify unprotected calls
 * and field mutations in smart contracts.
 */

// Internal imports ordered alphabetically by path
import {
  DataflowFact,
  IFDSResult,
  IFDSSolver,
} from "../../internals/ifds/ifds";
import { Cfg, CompilationUnit } from "../../internals/ir";
import { MistiTactWarning, Severity } from "../../internals/warnings";
import { DataflowDetector } from "../detector";
import {
  AstExpression,
  AstNode,
  AstStatement,
  idText,
} from "@tact-lang/compiler/dist/grammar/ast";
import { prettyPrint } from "@tact-lang/compiler/dist/prettyPrinter";

// Known send functions
const SEND_FUNCTIONS = ["send"];

// Known mutation methods that modify state in Tact (versions < 1.6)
const MUTATION_METHODS = new Set([
  // Slice mutation methods (available before Tact 1.6)
  "loadRef", // Loads the next reference from a Slice as a Cell
  "loadBit", // Loads a single bit from a Slice as a Bool (since Tact 1.5.0)
  "loadCoins", // Loads an unsigned Int (0 to 2^120 - 1) from a Slice
  "loadBits", // Loads a specified number of bits from a Slice as a new Slice
  "loadInt", // Loads a signed Int of specified bits from a Slice
  "loadUint", // Loads an unsigned Int of specified bits from a Slice

  // Additional mutation methods for other types or contexts
  "set", // Likely modifies a map or contract state by setting a value
  "del", // Likely deletes an entry from a map or contract state
  "add", // Likely adds an element to a map or data structure
  "remove", // Likely removes an element from a map or data structure
  "Slice", // Possibly a constructor or method related to Slice modification
]);

// Safe addresses and functions that don't need protection
const SAFE_ADDRESSES = ["myAddress()", "sender()", "this.owner"];

/**
 * Detector for unprotected calls and field mutations.
 *
 * ## Why is it bad?
 * Without conditions or permission checks, some calls can be exploited to
 * disrupt the contract's intended behavior or allow malicious actors to
 * perform unauthorized actions. For example, a publicly accessible `set`
 * function in a mapping or an unguarded `send` call can enable draining
 * contract's funds, denial-of-service (DoS) attacks or other malicious
 * activities.
 *
 * ## Example
 * ```tact
 * receive(msg: Insert) {
 *     // Bad: No protection for the mapping update
 *     m.set(msg.key, msg.val);
 * }
 * ```
 *
 * Use instead:
 * ```tact
 * receive(msg: Insert) {
 *     // OK: Permission check ensures only the owner can modify the state
 *     require(ctx.sender == this.owner, "Invalid sender");
 *     m.set(msg.key, msg.val);
 * }
 * ```
 */
export class UnprotectedCallIFDS extends DataflowDetector {
  severity = Severity.HIGH;

  async check(cu: CompilationUnit): Promise<MistiTactWarning[]> {
    const warnings: MistiTactWarning[] = [];

    try {
      // First pass: perform path-sensitive IFDS taint analysis
      const ifdsResults = new Map<string, IFDSResult>();
      const solver = new IFDSSolver(cu, true); // Enable path sensitivity

      // Run the analysis on each function
      cu.forEachCFG((cfg: Cfg) => {
        try {
          // Skip standard library functions for performance
          const func = cu.ast.getFunction(cfg.id);
          if (func && func.loc && func.loc.origin === "stdlib") {
            return; // Skip standard library functions
          }

          // Initialize with empty facts and solve
          const initialFacts = new Set<DataflowFact>();
          const result = solver.solve(cfg, initialFacts);

          // Store the result for this function
          const functionKey = cfg.id.toString();
          ifdsResults.set(functionKey, result);
        } catch (e) {
          // Ignore errors for specific functions
          this.ctx.logger?.debug?.(
            `Error analyzing function: ${e instanceof Error ? e.message : String(e)}`,
          );
        }
      });

      // Second pass: Analyze the results to find unprotected calls
      for (const [functionKey, result] of ifdsResults) {
        // Get the CFG for this function
        let cfg: Cfg | undefined;
        cu.forEachCFG((c) => {
          if (c.id.toString() === functionKey) {
            cfg = c;
          }
        });

        if (!cfg) continue;

        // Analyze all statements in this function for unprotected calls
        cfg.forEachBasicBlock(cu.ast, (stmt: AstStatement, bb) => {
          try {
            // Check if this statement is in a protected context
            const isProtected = this.isStatementProtected(stmt, result, bb.idx);

            // Skip if this statement is protected
            if (isProtected) {
              return;
            }

            // Look for taint sinks in the results for this basic block
            const blockFacts = result.getFacts(bb.idx);

            // Check for unprotected calls in the statement
            this.checkForUnprotectedCalls(stmt, blockFacts, warnings);
          } catch (e) {
            // Just log and continue if there's an error
            this.ctx.logger?.debug?.(
              `Error checking statement: ${e instanceof Error ? e.message : String(e)}`,
            );
          }
        });
      }
    } catch (e) {
      // Log the error and continue
      this.ctx.logger?.error?.(
        `Error in ${this.id}: ${e instanceof Error ? e.message : String(e)}`,
      );
    }

    return warnings;
  }

  /**
   * Check if a statement is executed in a protected context (e.g., after a permission check)
   */
  private isStatementProtected(
    stmt: AstStatement,
    result: IFDSResult,
    blockIdx: number,
  ): boolean {
    // Get facts for this statement
    const facts = result.getFacts(blockIdx);

    // Look for facts that indicate this statement is in a protected context
    for (const fact of facts) {
      // Check if this fact has a :protected-by: marker
      if (fact.id.includes(":protected-by:")) {
        return true;
      }

      // Check if this fact has a path context with permission checks
      if (fact.context && fact.context.conditions) {
        for (const [_condId, value] of fact.context.conditions) {
          // If this is a permission check condition and it's true, the statement is protected
          if (this.isPermissionCheckCondition(_condId) && value === true) {
            return true;
          }
        }
      }
    }

    // For backward compatibility, also use the heuristic check
    if (this.isInProtectedBlock(stmt)) {
      return true;
    }

    return false;
  }

  /**
   * Checks if a condition is a permission check based on condition ID.
   * This would be more accurate in a full implementation where we track condition types.
   */
  private isPermissionCheckCondition(_condId: AstNode["id"]): boolean {
    // This is a placeholder - in a full implementation, we would track which
    // conditions are permission checks during analysis
    return false;
  }

  /**
   * Heuristically check if a statement is in a protected block.
   * This is a simplified version of the previous approach for backward compatibility.
   */
  private isInProtectedBlock(stmt: AstStatement): boolean {
    // Simple heuristic - check if the statement is inside a conditional block
    // with a permission check-like condition
    if (stmt.kind === "statement_condition") {
      return this.isPermissionCheck(stmt.condition);
    }

    // For other statements, we don't have context information
    return false;
  }

  /**
   * Check for unprotected calls using the taint analysis results.
   */
  private checkForUnprotectedCalls(
    stmt: AstStatement,
    blockFacts: Set<DataflowFact>,
    warnings: MistiTactWarning[],
  ): void {
    // Only process expression statements
    if (stmt.kind !== "statement_expression") return;

    const expr = stmt.expression;

    // Check for map mutations
    if (expr.kind === "method_call" && expr.method) {
      const methodName = idText(expr.method);

      // Handle all mutation methods
      if (
        MUTATION_METHODS.has(methodName) &&
        expr.self &&
        expr.self.kind === "field_access"
      ) {
        this.checkMapMutation(expr, warnings, blockFacts);
        return;
      }
    }

    // Check for send calls
    if (expr.kind === "static_call" && expr.function) {
      const fnName = idText(expr.function);

      // Handle send function
      if (
        SEND_FUNCTIONS.includes(fnName) &&
        expr.args &&
        expr.args.length > 0
      ) {
        this.checkSendCall(expr, warnings, blockFacts);
        return;
      }
    }

    // Also check for taint sinks in general
    const sinkFacts = Array.from(blockFacts).filter(
      (fact) =>
        fact.node === expr.id &&
        (fact.id.includes(":taint-sink:send") ||
          fact.id.includes(":taint-sink:mutation")),
    );

    if (sinkFacts.length > 0) {
      warnings.push(
        this.makeWarning(
          `Unprotected operation with tainted values: ${prettyPrint(expr)}`,
          expr.loc,
        ),
      );
    }
  }

  /**
   * Check if a condition is a permission check.
   */
  private isPermissionCheck(expr: AstExpression): boolean {
    if (expr.kind === "op_binary") {
      const op = expr.op;

      // Check for equality operations
      if (op === "==" || op === "!=") {
        // Check for comparisons with sender or owner
        const leftText = prettyPrint(expr.left);
        const rightText = prettyPrint(expr.right);

        // Check for sender() == owner or similar patterns
        if (
          leftText.includes("sender") ||
          rightText.includes("sender") ||
          leftText.includes("owner") ||
          rightText.includes("owner")
        ) {
          return true;
        }

        // Check for address validity checks
        if (
          (leftText.includes("Address") || rightText.includes("Address")) &&
          (leftText.includes("newAddress") || rightText.includes("newAddress"))
        ) {
          return true;
        }
      }
    } else if (expr.kind === "static_call") {
      // Check for require() calls
      if (
        expr.function &&
        expr.function.kind === "id" &&
        idText(expr.function) === "require"
      ) {
        return true;
      }
    } else if (expr.kind === "method_call") {
      // Check for method calls like checkAddr
      if (
        expr.method &&
        expr.method.kind === "id" &&
        (idText(expr.method).includes("check") ||
          idText(expr.method).includes("valid"))
      ) {
        return true;
      }
    }

    return false;
  }

  /**
   * Legacy method for checking send calls.
   */
  private checkSendCall(
    call: AstExpression & { function?: AstNode; args?: AstExpression[] },
    warnings: MistiTactWarning[],
    facts: Set<DataflowFact>,
  ): void {
    // Get the first argument (SendParameters)
    const sendParamsArg = call.args?.[0];
    if (!sendParamsArg || sendParamsArg.kind !== "struct_instance") {
      return;
    }

    // Check if any args are tainted based on facts
    const isTainted = Array.from(facts).some(
      (fact) => sendParamsArg.id === fact.node && fact.id.includes(":taint:"),
    );

    // Check for safe addresses in the SendParameters
    const sendParamsText = prettyPrint(sendParamsArg);
    if (SAFE_ADDRESSES.some((addr) => sendParamsText.includes(addr))) {
      return; // Safe address, no warning needed
    }

    warnings.push(
      this.makeWarning(
        `Unprotected send with potentially unsafe arguments${isTainted ? " (tainted)" : ""}: ${prettyPrint(sendParamsArg)}`,
        sendParamsArg.loc,
      ),
    );
  }

  /**
   * Legacy method for checking map mutations.
   */
  private checkMapMutation(
    call: AstExpression & { method?: AstNode; args?: AstExpression[] },
    warnings: MistiTactWarning[],
    facts: Set<DataflowFact>,
  ): void {
    if (!call.args || call.args.length === 0) return;

    // Check if any of the arguments are tainted
    const isTainted = call.args.some((arg) => {
      // Check if this specific argument has a taint fact
      return Array.from(facts).some(
        (fact) => fact.node === arg.id && fact.id.includes(":taint:"),
      );
    });

    // Check for known safe constants like numeric literals or safe addresses
    const isExplicitlySafe = call.args.every((arg) => {
      // Check for numeric literals - compare the kind string directly
      if (arg.kind === "number") return true;

      // Check for safe addresses
      const argText = prettyPrint(arg);
      return SAFE_ADDRESSES.some((addr) => argText === addr);
    });

    // If tainted or not explicitly safe, generate a warning
    if (isTainted || !isExplicitlySafe) {
      warnings.push(
        this.makeWarning(
          `Unprotected field mutation${isTainted ? " with tainted values" : ""}: ${prettyPrint(call)}`,
          call.loc,
        ),
      );
    }
  }
}
