import { BasicBlock, CompilationUnit, Cfg } from "../ir";
import { Transfer } from "../transfer";
// These imports are used for type information
// eslint-disable-next-line @typescript-eslint/no-unused-vars, unused-imports/no-unused-imports
import { DataflowFact, PathContext } from "./ifds";
import {
  AstNode,
  AstExpression,
  AstStatement,
  // eslint-disable-next-line @typescript-eslint/no-unused-vars, unused-imports/no-unused-imports
  AstId,
  idText,
} from "@tact-lang/compiler/dist/grammar/ast";
import { prettyPrint } from "@tact-lang/compiler/dist/prettyPrinter";

/**
 * Transfer function for IFDS analysis.
 *
 * This transfer function implements the path-sensitive interprocedural analysis
 * with support for:
 * - Path sensitivity through condition tracking
 * - Interprocedural analysis through function call handling
 * - Field tracking for contract state variables
 * - Loop handling with limited unrolling
 */
export class IFDSTransfer implements Transfer<Set<DataflowFact>> {
  private readonly cu: CompilationUnit;
  private readonly pathSensitive: boolean;
  private readonly summaryEdges: Map<
    string,
    Map<DataflowFact, Set<DataflowFact>>
  >;
  private readonly maxLoopUnrolling: number;
  private readonly loopCounts: Map<number, number> = new Map(); // Track loop iterations

  /**
   * Creates a new IFDS transfer function.
   *
   * @param cu The compilation unit
   * @param pathSensitive Whether to perform path-sensitive analysis
   * @param summaryEdges Summary edges for interprocedural analysis
   * @param maxLoopUnrolling Maximum number of times to unroll loops
   */
  constructor(
    cu: CompilationUnit,
    pathSensitive: boolean,
    summaryEdges: Map<string, Map<DataflowFact, Set<DataflowFact>>>,
    maxLoopUnrolling: number = 2,
  ) {
    this.cu = cu;
    this.pathSensitive = pathSensitive;
    this.summaryEdges = summaryEdges;
    this.maxLoopUnrolling = maxLoopUnrolling;
  }

  /**
   * Identifies taint sources in the code and marks them in the IFDS facts.
   * This is a simplified version that handles common taint sources.
   *
   * @param outState The dataflow facts to update
   * @param bb The entry basic block
   * @param cfg The CFG containing the basic block
   */
  public identifyTaintSources(
    outState: Set<DataflowFact>,
    bb: BasicBlock,
    cfg: Cfg | undefined,
  ): void {
    // Skip if path sensitivity is disabled
    if (!this.pathSensitive) {
      return;
    }

    // In a security analysis, we consider certain inputs as tainted by default:
    // 1. Message parameters in receive methods
    // 2. External function parameters
    // 3. sender() calls
    // 4. Contract fields (state variables)

    // Mark standard taint sources
    const entryTaintFact: DataflowFact = {
      id: `entry:taint:source`,
      node: bb.idx,
      context: undefined, // No path context initially
    };
    outState.add(entryTaintFact);

    // Taint from sender() calls
    const senderTaintFact: DataflowFact = {
      id: `sender:taint:source`,
      node: bb.idx,
      context: undefined,
    };
    outState.add(senderTaintFact);

    // If we don't have a cfg, we can't identify function-specific taint sources
    if (!cfg) return;

    // Find the function AST node for this CFG to get parameters
    const funcAst = this.cu.ast.getFunction(cfg.id);
    if (funcAst) {
      // Taint function parameters for receive methods
      // Use type assertion to handle different AST function types
      const funcDef = funcAst as any;
      if (
        funcDef.kind === "function_def" &&
        funcDef.name &&
        funcDef.name.kind === "id" &&
        funcDef.args
      ) {
        const funcName = idText(funcDef.name);
        // Parameters in receive methods are tainted (user-controlled)
        if (funcName.startsWith("receive")) {
          for (const arg of funcDef.args) {
            if (arg.name && arg.name.id) {
              const paramTaintFact: DataflowFact = {
                id: `${arg.name.id}:taint:param`,
                node: arg.name.id,
                context: undefined,
              };
              outState.add(paramTaintFact);
            }
          }
        }
      }

      // Taint contract fields - these are considered sensitive
      // Get contract fields by finding the receiver's contract type
      const contractFields: AstNode[] = [];
      try {
        // Use type assertion to access receiver property
        const funcWithReceiver = funcAst as any;
        if (funcWithReceiver.receiver && funcWithReceiver.receiver.type) {
          // Get the contract fields from the AST
          const contracts = Array.from(this.cu.ast.getContracts?.() || []);
          for (const contract of contracts) {
            try {
              const astContract = this.cu.ast.getContract?.(contract.id);
              if (astContract && astContract.declarations) {
                // Add field declarations as taint sources
                for (const decl of astContract.declarations) {
                  if (decl.kind === "field_decl" && decl.name) {
                    contractFields.push(decl.name);
                    const fieldTaintFact: DataflowFact = {
                      id: `${decl.name.id}:taint:field`,
                      node: decl.name.id,
                      context: undefined,
                    };
                    outState.add(fieldTaintFact);
                  }
                }
              }
            } catch (e) {
              // Ignore errors for specific contracts
            }
          }
        }
      } catch (e) {
        // Silently ignore errors during field extraction
      }
    }
  }

  /**
   * Implements the IFDS transfer function.
   *
   * @param inState The incoming state (set of facts)
   * @param bb The basic block to analyze
   * @param stmt The statement in the basic block
   * @returns The outgoing state (set of facts)
   */
  public transfer(
    inState: Set<DataflowFact>,
    bb: BasicBlock,
    stmt: AstStatement,
  ): Set<DataflowFact> {
    // Create a working copy of the input state
    const outState = new Set<DataflowFact>(inState);

    // For entry blocks, identify taint sources
    if (bb.idx === 0) {
      this.identifyTaintSources(outState, bb, this.getCfgForBasicBlock(bb));
    }

    // Handle loops - if we've exceeded the unrolling limit, apply approximation
    if (this.isLoopHeader(bb)) {
      const loopCount = this.loopCounts.get(bb.idx) || 0;
      this.loopCounts.set(bb.idx, loopCount + 1);

      if (loopCount >= this.maxLoopUnrolling) {
        // Over the unrolling limit - apply approximation by dropping path information
        this.approximateLoopFacts(outState);
        return outState;
      }
    }

    // Handle different types of statements
    switch (stmt.kind) {
      case "statement_condition":
        this.handleCondition(
          outState,
          stmt as AstStatement & { condition: AstExpression },
        );
        break;

      case "statement_let":
      case "statement_assign":
      case "statement_augmentedassign":
        this.handleAssignment(outState, stmt);
        break;

      case "statement_return":
        this.handleReturn(
          outState,
          stmt as AstStatement & { expression?: AstExpression },
          bb,
        );
        break;

      case "statement_expression":
        this.handleExpression(
          outState,
          stmt as AstStatement & { expression: AstExpression },
        );
        break;

      // Handle other statement types
      case "statement_while":
      case "statement_until":
      case "statement_repeat":
      case "statement_try":
      case "statement_try_catch":
      case "statement_foreach":
        // For these statements, we don't have specialized handling yet
        break;
    }

    return outState;
  }

  /**
   * Handles conditional statements, updating path contexts for facts.
   *
   * In path-sensitive taint analysis, it's critical to track which conditions a fact
   * is valid under. This function creates new facts for both branches of a condition,
   * maintaining separate path contexts for each branch.
   *
   * For permission checks, facts in the true branch are marked as being under
   * a permission check, which is used later to determine if a sink is protected.
   */
  private handleCondition(
    outState: Set<DataflowFact>,
    stmt: AstStatement & { condition: AstExpression },
  ): void {
    // Skip path-sensitive handling if pathSensitive is false
    if (!this.pathSensitive) {
      return; // Skip path context tracking if path sensitivity is disabled
    }

    const condId = stmt.condition.id;

    // Check if this condition is a permission check
    const isPermissionCheck = this.isPermissionCheck(stmt.condition);

    // For each fact in the state, create two new facts:
    // - One for the true branch with condition=true
    // - One for the false branch with condition=false
    const factsToAdd: DataflowFact[] = [];

    for (const fact of outState) {
      // Create new fact for true branch with updated path context
      const trueFact = { ...fact };
      if (!trueFact.context) {
        trueFact.context = { conditions: new Map() };
      } else {
        // Clone the context to avoid modifying the original
        trueFact.context = {
          conditions: new Map(trueFact.context.conditions),
        };
      }
      trueFact.context.conditions.set(condId, true);

      // If this is a permission check, mark the fact with a special attribute
      if (isPermissionCheck) {
        trueFact.id = `${trueFact.id}:protected-by:${condId}`;
      }

      factsToAdd.push(trueFact);

      // Create new fact for false branch with updated path context
      const falseFact = { ...fact };
      if (!falseFact.context) {
        falseFact.context = { conditions: new Map() };
      } else {
        // Clone the context to avoid modifying the original
        falseFact.context = {
          conditions: new Map(falseFact.context.conditions),
        };
      }
      falseFact.context.conditions.set(condId, false);
      factsToAdd.push(falseFact);
    }

    // Add all the new facts to the output state
    for (const fact of factsToAdd) {
      outState.add(fact);
    }
  }

  /**
   * Checks if a condition is a permission check.
   *
   * Permission checks typically compare sender addresses with authorized addresses
   * like owner, or validate addresses through require() statements.
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
          (leftText.includes("sender") && rightText.includes("owner")) ||
          (rightText.includes("sender") && leftText.includes("owner"))
        ) {
          return true;
        }

        // Check for direct sender comparisons
        if (leftText.includes("sender") || rightText.includes("sender")) {
          return true;
        }
      }
    } else if (expr.kind === "static_call") {
      // Check for require() calls with sender-related conditions
      if (
        expr.function &&
        expr.function.kind === "id" &&
        idText(expr.function) === "require" &&
        expr.args &&
        expr.args.length > 0
      ) {
        const requireConditionText = prettyPrint(expr.args[0]);
        if (
          requireConditionText.includes("sender") ||
          requireConditionText.includes("owner")
        ) {
          return true;
        }
      }
    }

    return false;
  }

  /**
   * Handles assignment statements, tracking taint flow.
   */
  private handleAssignment(
    outState: Set<DataflowFact>,
    stmt: AstStatement,
  ): void {
    let lhs: AstNode | undefined;
    let rhs: AstExpression | undefined;

    if (stmt.kind === "statement_let") {
      lhs = (stmt as any).name;
      rhs = (stmt as any).expression;
    } else if (stmt.kind === "statement_assign") {
      lhs = (stmt as any).path;
      rhs = (stmt as any).expression;
    } else if (stmt.kind === "statement_augmentedassign") {
      lhs = (stmt as any).path;
      rhs = (stmt as any).expression;
    }

    if (!lhs || !rhs) return;

    // Find facts related to RHS
    const rhsFacts = this.getFactsForNode(outState, rhs.id);

    // For each RHS fact, create a corresponding LHS fact
    for (const rhsFact of rhsFacts) {
      const newFact: DataflowFact = {
        id: `${lhs.id}:taint`,
        node: lhs.id,
        context: rhsFact.context,
      };

      outState.add(newFact);
    }

    // Handle special cases like struct initializations, etc.
    if (rhs.kind === "struct_instance") {
      // Add taint for struct fields
    } else if (rhs.kind === "method_call") {
      // Handle method calls
      this.handleMethodCall(
        outState,
        rhs as AstExpression & { method?: AstNode },
        lhs,
      );
    }
  }

  /**
   * Handles method calls in assignments.
   */
  private handleMethodCall(
    outState: Set<DataflowFact>,
    call: AstExpression & { method?: AstNode },
    lhs: AstNode,
  ): void {
    if (!call.method) return;

    // Find callee function/method
    const calleeCfg = this.findCalleeCfg(call);

    if (calleeCfg) {
      // Use summary edges if available
      const calleeKey = `${calleeCfg.id}`;
      if (this.summaryEdges.has(calleeKey)) {
        const summaries = this.summaryEdges.get(calleeKey)!;

        // Apply summary edges
        for (const fact of outState) {
          const summaryResults = summaries.get(fact);
          if (summaryResults) {
            for (const resultFact of summaryResults) {
              outState.add(resultFact);
            }
          }
        }
      } else {
        // Create a simple approximation for the call result
        const newFact: DataflowFact = {
          id: `${lhs.id}:taint-from-call`,
          node: lhs.id,
          context: undefined, // Reset path context as we don't have precise call info
        };

        outState.add(newFact);
      }
    }
  }

  /**
   * Handles return statements, creating summary edges.
   */
  private handleReturn(
    outState: Set<DataflowFact>,
    stmt: AstStatement & { expression?: AstExpression },
    bb: BasicBlock,
  ): void {
    if (!stmt.expression) return;

    // Find facts for the return expression
    const returnFacts = this.getFactsForNode(outState, stmt.expression.id);

    // Create/update summary edges for this function
    const cfg = this.getCfgForBasicBlock(bb);
    if (cfg) {
      const summaryKey = `${cfg.id}`;

      // For each input fact, map to return facts
      for (const inFact of outState) {
        if (!this.summaryEdges.has(summaryKey)) {
          this.summaryEdges.set(summaryKey, new Map());
        }

        const functionSummary = this.summaryEdges.get(summaryKey)!;

        if (!functionSummary.has(inFact)) {
          functionSummary.set(inFact, new Set());
        }

        const resultFacts = functionSummary.get(inFact)!;

        for (const returnFact of returnFacts) {
          resultFacts.add(returnFact);
        }
      }
    }
  }

  /**
   * Handles expression statements (method calls, etc.).
   */
  private handleExpression(
    outState: Set<DataflowFact>,
    stmt: AstStatement & { expression: AstExpression },
  ): void {
    const expr = stmt.expression;

    if (expr.kind === "method_call") {
      // Handle method calls that could propagate taint
      this.handleMethodCallExpression(
        outState,
        expr as AstExpression & {
          method?: AstNode;
          args?: AstExpression[];
          self?: AstExpression;
        },
      );
    } else if (expr.kind === "static_call") {
      // Handle static calls
    }
  }

  /**
   * Handles method call expressions with enhanced taint tracking.
   */
  private handleMethodCallExpression(
    outState: Set<DataflowFact>,
    call: AstExpression & {
      method?: AstNode;
      args?: AstExpression[];
      self?: AstExpression;
    },
  ): void {
    if (!call.method) return;

    // Skip taint propagation in method calls if pathSensitive is disabled
    if (!this.pathSensitive) {
      return;
    }

    // Track taint for security-sensitive methods
    // Safely get method name, verifying it's an id
    let methodName = "";
    if (call.method.kind === "id") {
      methodName = idText(call.method);
    } else {
      return; // Not a simple method we can analyze
    }

    // Handle interprocedural analysis with the call graph
    const calleeCfg = this.findCalleeCfg(call);
    if (calleeCfg) {
      // Propagate taint through the call if we have tainted arguments
      let _hasTaintedArgs = false; // Prefix with underscore to indicate deliberate unused variable
      if (call.args) {
        for (const arg of call.args) {
          const argFacts = this.getFactsForNode(outState, arg.id);
          if (argFacts.size > 0) {
            _hasTaintedArgs = true;
            // A full interprocedural analysis would map arguments to parameters here
            // For now, we'll mark the call as tainted
            const callTaintFact: DataflowFact = {
              id: `${call.id}:taint:call-with-tainted-args`,
              node: call.id,
              context: argFacts.values().next().value?.context,
            };
            outState.add(callTaintFact);
          }
        }
      }

      // For self references which may be fields, mark those as possibly tainted too
      if (call.self && call.self.kind === "field_access") {
        const selfFacts = this.getFactsForNode(outState, call.self.id);
        if (selfFacts.size > 0) {
          _hasTaintedArgs = true;
          // Mark the call itself as tainted
          const selfTaintFact: DataflowFact = {
            id: `${call.id}:taint:call-with-tainted-self`,
            node: call.id,
            context: selfFacts.values().next().value?.context,
          };
          outState.add(selfTaintFact);
        }
      }
    }

    // Handle send() calls - these are security-sensitive operations
    if (methodName === "send" && call.args && call.args.length > 0) {
      // The first argument to send is typically SendParameters, which may contain tainted data
      const sendParams = call.args[0];
      if (sendParams) {
        // Check if the sendParams or any of its fields are tainted
        const sendParamFacts = this.getFactsForNode(outState, sendParams.id);

        if (sendParamFacts.size > 0) {
          // Mark this send call as a taint sink with a special fact
          const sinkFact: DataflowFact = {
            id: `${call.id}:taint-sink:send`,
            node: call.id,
            // Preserve context to track if this occurs in a protected context
            context: sendParamFacts.values().next().value?.context,
          };

          outState.add(sinkFact);
        }

        // Also check fields like 'to', 'value', 'body', etc. if it's a struct instance
        if (sendParams.kind === "struct_instance") {
          this.checkStructFieldsForTaint(
            outState,
            sendParams as any,
            call.id,
            "send",
          );
        }
      }
    }

    // Handle map mutations (set, del, etc.) - these can expose sensitive state
    if (
      ["set", "del", "add", "remove"].includes(methodName) &&
      call.self &&
      call.args &&
      call.args.length > 0
    ) {
      // Check if the container (self) is a sensitive container (mapping, etc.)
      const containerFacts = this.getFactsForNode(outState, call.self.id);
      const isSensitiveContainer =
        containerFacts.size > 0 || call.self.kind === "field_access"; // field accesses are sensitive

      // Check if any arguments are tainted
      const argFacts: Set<DataflowFact> = new Set();
      for (const arg of call.args) {
        const facts = this.getFactsForNode(outState, arg.id);
        for (const fact of facts) {
          argFacts.add(fact);
        }
      }

      // If we have sensitive container or tainted args, mark as sink
      if (isSensitiveContainer || argFacts.size > 0) {
        // Create a taint sink fact for this mutation
        const sinkFact: DataflowFact = {
          id: `${call.id}:taint-sink:mutation`,
          node: call.id,
          // Preserve context (if any) from arg or container
          context:
            argFacts.size > 0
              ? argFacts.values().next().value?.context
              : containerFacts.values().next().value?.context,
        };

        outState.add(sinkFact);
      }
    }
  }

  /**
   * Checks fields of a struct instance for taint and creates sink facts if needed.
   */
  private checkStructFieldsForTaint(
    outState: Set<DataflowFact>,
    struct: AstExpression & {
      fields?: Array<{ name: AstNode; value: AstExpression }>;
    },
    callId: AstNode["id"],
    sinkType: string,
  ): void {
    if (!struct.fields) return;

    for (const field of struct.fields) {
      if (!field.value) continue;

      const fieldFacts = this.getFactsForNode(outState, field.value.id);
      if (fieldFacts.size > 0) {
        // Create a taint sink fact for this field
        const fieldName =
          field.name.kind === "id"
            ? idText(field.name)
            : `field_${field.name.id}`;
        const sinkFact: DataflowFact = {
          id: `${callId}:taint-sink:${sinkType}:${fieldName}`,
          node: callId,
          context: fieldFacts.values().next().value?.context,
        };

        outState.add(sinkFact);
      }

      // Recursively check nested structs
      if (field.value.kind === "struct_instance") {
        const fieldName =
          field.name.kind === "id"
            ? idText(field.name)
            : `field_${field.name.id}`;
        this.checkStructFieldsForTaint(
          outState,
          field.value as any,
          callId,
          `${sinkType}:${fieldName}`,
        );
      }
    }
  }

  /**
   * Gets all facts related to a specific AST node.
   */
  private getFactsForNode(
    facts: Set<DataflowFact>,
    nodeId: AstNode["id"],
  ): Set<DataflowFact> {
    const result = new Set<DataflowFact>();

    for (const fact of facts) {
      if (fact.node === nodeId) {
        result.add(fact);
      }
    }

    return result;
  }

  /**
   * Checks if a basic block is a loop header.
   */
  private isLoopHeader(bb: BasicBlock): boolean {
    // In a real implementation, we would use dominator information
    // Here we make a simplification and check if any incoming edge is a back edge
    return bb.idx > 0; // Simplified check, assumes any non-entry block might be a loop header
  }

  /**
   * Approximates loop facts by removing path context information.
   * This is to prevent infinite loop unrolling while maintaining soundness.
   */
  private approximateLoopFacts(facts: Set<DataflowFact>): void {
    // If path sensitivity is disabled, no need for approximation
    if (!this.pathSensitive) {
      return;
    }

    // For each fact, remove path context to approximate the loop effect
    const approximatedFacts = new Set<DataflowFact>();
    for (const fact of facts) {
      // Create a copy without path context
      const approximatedFact = { ...fact, context: undefined };
      approximatedFacts.add(approximatedFact);
    }

    // Replace the original facts with the approximated ones
    facts.clear();
    for (const fact of approximatedFacts) {
      facts.add(fact);
    }
  }

  /**
   * Finds the CFG for a function call using the call graph.
   */
  private findCalleeCfg(
    call: AstExpression & { method?: AstNode },
  ): Cfg | undefined {
    if (!call.method) return undefined;

    // Look up the method name
    let methodName = "";
    if (call.method.kind === "id") {
      methodName = idText(call.method);
    } else {
      return undefined;
    }

    // Use the compilation unit's call graph to find the callee
    try {
      let found: Cfg | undefined = undefined;

      // Search through all CFGs to find a matching method name
      this.cu.forEachCFG((cfg) => {
        const funcId = cfg.id;
        const func = this.cu.ast.getFunction(funcId);

        if (func) {
          // Use type assertion to handle different function types
          const funcWithName = func as any;
          if (
            funcWithName.name &&
            funcWithName.name.kind === "id" &&
            idText(funcWithName.name) === methodName
          ) {
            found = cfg;
          }
        }
      });

      return found;
    } catch (e) {
      // Ignore errors in call graph traversal
      return undefined;
    }
  }

  /**
   * Gets the CFG containing a basic block.
   */
  private getCfgForBasicBlock(bb: BasicBlock): Cfg | undefined {
    for (const cfg of this.getAllCfgs()) {
      if (cfg.nodes.some((node) => node.idx === bb.idx)) {
        return cfg;
      }
    }
    return undefined;
  }

  /**
   * Gets all CFGs in the compilation unit.
   */
  private getAllCfgs(): Cfg[] {
    const cfgs: Cfg[] = [];
    this.cu.forEachCFG((cfg) => cfgs.push(cfg));
    return cfgs;
  }
}
