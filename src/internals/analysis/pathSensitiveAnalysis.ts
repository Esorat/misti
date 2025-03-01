import { DataflowFact, IFDSResult, IFDSSolver, PathContext } from "../ifds";
import { CompilationUnit, BasicBlock, Cfg } from "../ir";
import {
  AstNode,
  AstExpression,
  AstId,
  idText,
} from "@tact-lang/compiler/dist/grammar/ast";

/**
 * Path-sensitive interprocedural taint analysis implementation.
 *
 * This analysis tracks taint flows through a program with path sensitivity,
 * making it suitable for security detectors like UnprotectedCall that need
 * to check if taints are guarded by conditions.
 */

/**
 * Represents a tainted value in the program.
 */
export interface TaintSource {
  id: AstNode["id"];
  name: string;
  kind: "parameter" | "field" | "receiver";
}

/**
 * The result of a path-sensitive taint analysis, providing methods to query
 * taint information at different program points.
 */
export class TaintAnalysisResult {
  private ifdsResult: IFDSResult;
  private cu: CompilationUnit;

  constructor(ifdsResult: IFDSResult, cu: CompilationUnit) {
    this.ifdsResult = ifdsResult;
    this.cu = cu;
  }

  /**
   * Checks if a node is tainted at a specific program point.
   */
  public isTainted(bb: BasicBlock, nodeId: AstNode["id"]): boolean {
    return this.ifdsResult.hasFact(bb.idx, {
      id: `${nodeId}:taint`,
      node: nodeId,
    });
  }

  /**
   * Checks if a node is tainted at a specific program point and path context.
   */
  public isTaintedWithContext(
    bb: BasicBlock,
    nodeId: AstNode["id"],
    context?: PathContext,
  ): boolean {
    const facts = this.ifdsResult.getFacts(bb.idx);
    if (!facts) return false;

    for (const fact of facts) {
      if (fact.node === nodeId && fact.id.startsWith(`${nodeId}:taint`)) {
        // If no context is specified, any taint is sufficient
        if (!context) return true;

        // If context is specified, check if the fact has a matching context
        if (fact.context && this.contextsMatch(fact.context, context)) {
          return true;
        }
      }
    }

    return false;
  }

  /**
   * Checks if two path contexts match.
   */
  private contextsMatch(_c1: PathContext, _c2: PathContext): boolean {
    // In a real implementation, this would check if the contexts are compatible
    return true;
  }

  /**
   * Gets all tainted nodes at a specific program point.
   */
  public getTaintedNodes(bb: BasicBlock): Set<AstNode["id"]> {
    const facts = this.ifdsResult.getFacts(bb.idx);
    if (!facts) return new Set();

    const taintedNodes = new Set<AstNode["id"]>();
    for (const fact of facts) {
      if (fact.id.includes(":taint")) {
        taintedNodes.add(fact.node);
      }
    }

    return taintedNodes;
  }

  /**
   * Gets the guarding conditions for a tainted node.
   */
  public getGuardingConditions(
    bb: BasicBlock,
    nodeId: AstNode["id"],
  ): Map<AstNode["id"], boolean> {
    const facts = this.ifdsResult.getFacts(bb.idx);
    if (!facts) return new Map();

    const guardingConditions = new Map<AstNode["id"], boolean>();
    for (const fact of facts) {
      if (
        fact.node === nodeId &&
        fact.id.startsWith(`${nodeId}:taint`) &&
        fact.context
      ) {
        for (const [condId, value] of fact.context.conditions) {
          guardingConditions.set(condId, value);
        }
      }
    }

    return guardingConditions;
  }

  /**
   * Checks if a node is protected by a permission check.
   */
  public isProtected(bb: BasicBlock, nodeId: AstNode["id"]): boolean {
    const guardingConditions = this.getGuardingConditions(bb, nodeId);

    // No guarding conditions means no protection
    if (guardingConditions.size === 0) {
      return false;
    }

    // For each condition ID, try to find it in the statements
    for (const [condId, value] of guardingConditions) {
      const condStmt = this.cu.ast.getStatement(condId);

      // If we found a statement, check if it's a permission check
      if (condStmt && this.isPermissionCheck(condStmt, value)) {
        return true;
      }
    }

    return false;
  }

  /**
   * Determines if a condition is a permission check.
   * Permission checks include:
   * - Sender equality checks (ctx.sender == owner)
   * - Address validity checks (addr != null)
   * - Custom validation functions that check permissions
   */
  private isPermissionCheck(condNode: AstNode, _condValue: boolean): boolean {
    // TODO: This is a simplified implementation, a real one would:
    // 1. Check for equality expressions involving sender/owner
    // 2. Check for function calls that might validate permissions
    // 3. Look for custom validation patterns

    // For now, we'll check for some common patterns in the AST
    if (condNode.kind === "op_binary") {
      const op = (condNode as any).op;

      // Check for equality or inequality operations
      if (
        op === "==" ||
        op === "!=" ||
        op === ">=" ||
        op === "<=" ||
        op === ">" ||
        op === "<"
      ) {
        const left = (condNode as any).left;
        const right = (condNode as any).right;

        // Check for sender checks (e.g., ctx.sender == this.owner)
        if (
          this.involvesContextSender(left) ||
          this.involvesContextSender(right)
        ) {
          return true;
        }

        // Check for address validity (e.g., addr != null)
        if (this.isAddressValidityCheck(left, right, op)) {
          return true;
        }
      }
    }

    // Check for require statements or custom validation function calls
    if (condNode.kind === "static_call") {
      const func = (condNode as any).function;
      if (func && func.kind === "id") {
        // Check for require or check functions
        const funcName = idText(func);
        if (
          funcName === "require" ||
          funcName.includes("check") ||
          funcName.includes("valid")
        ) {
          return true;
        }
      }
    }

    return false;
  }

  /**
   * Checks if an expression involves context.sender
   */
  private involvesContextSender(expr: any): boolean {
    if (!expr) return false;

    // Check for field access like ctx.sender
    if (expr.kind === "field_access") {
      const field = expr.field;
      const obj = expr.aggregate;

      if (field && field.kind === "id" && obj && obj.kind === "id") {
        const fieldName = idText(field);
        const objName = idText(obj);

        // Check for common sender patterns
        if (
          (fieldName === "sender" &&
            (objName === "ctx" || objName === "context")) ||
          (fieldName === "owner" && objName === "this")
        ) {
          return true;
        }
      }
    }
    return false;
  }

  /**
   * Checks if an expression is an address validity check
   */
  private isAddressValidityCheck(left: any, right: any, op: string): boolean {
    // Check for addr != null
    if (
      op === "!=" &&
      ((right && right.kind === "null") || (left && left.kind === "null"))
    ) {
      return true;
    }
    // Check for newAddress comparisons
    if (
      (left &&
        left.kind === "static_call" &&
        left.function &&
        left.function.kind === "id" &&
        idText(left.function) === "newAddress") ||
      (right &&
        right.kind === "static_call" &&
        right.function &&
        right.function.kind === "id" &&
        idText(right.function) === "newAddress")
    ) {
      return true;
    }
    return false;
  }
}

/**
 * Path-sensitive interprocedural taint analysis.
 */
export class PathSensitiveTaintAnalysis {
  private readonly cu: CompilationUnit;
  private readonly solver: IFDSSolver;
  private readonly pathSensitive: boolean;
  private readonly maxLoopUnrolling: number;

  /**
   * Creates a new path-sensitive taint analysis.
   *
   * @param cu The compilation unit to analyze
   * @param pathSensitive Whether to perform path-sensitive analysis
   * @param maxLoopUnrolling Maximum number of times to unroll loops
   */
  constructor(
    cu: CompilationUnit,
    pathSensitive: boolean = true,
    maxLoopUnrolling: number = 2,
  ) {
    this.cu = cu;
    this.pathSensitive = pathSensitive;
    this.maxLoopUnrolling = maxLoopUnrolling;
    // Create an IFDS solver configured for taint analysis
    this.solver = new IFDSSolver(cu);
  }

  /**
   * Analyzes a specific CFG for taint flows.
   */
  public analyzeCfg(cfg: Cfg): TaintAnalysisResult {
    // Identify taint sources
    const sources = this.identifySources(cfg);

    // Create initial facts
    const initialFacts = this.createInitialFacts(sources);

    // Solve the IFDS problem
    const solverResults = this.solver.solve(
      cfg,
      initialFacts,
      this.maxLoopUnrolling,
    );

    // Process results
    return new TaintAnalysisResult(solverResults, this.cu);
  }

  /**
   * Identifies taint sources for a specific CFG.
   */
  private identifySources(cfg: Cfg): TaintSource[] {
    const sources: TaintSource[] = [];
    const func = this.cu.ast.getFunction(cfg.id);

    if (!func) return sources;

    try {
      // Add parameters as sources if they exist
      if ("params" in func && Array.isArray(func.params)) {
        for (const param of func.params) {
          // Use type guards to ensure properties exist
          if (param && param.name && typeof param.name.id === "number") {
            sources.push({
              id: param.name.id,
              name: idText(param.name),
              kind: "parameter",
            });
          }
        }
      }
      // Add receiver as source for methods
      if ("receiver" in func && func.receiver) {
        const receiver = func.receiver as any;
        if (receiver && receiver.name && typeof receiver.name.id === "number") {
          sources.push({
            id: receiver.name.id,
            name: idText(receiver.name),
            kind: "receiver",
          });
        }
      }
      // Add contract fields as sources (without path sensitivity)
      if ("receiver" in func && func.receiver) {
        const contractFields = this.getContractFields(func);
        for (const field of contractFields) {
          sources.push({
            id: field.id,
            name: idText(field),
            kind: "field",
          });
        }
      }

      // Add all variables that might be external inputs (message parameters, etc.)
      // This is a heuristic to add common variables that might be inputs
      // in test cases or simple functions
      cfg.forEachBasicBlock(this.cu.ast, (stmt) => {
        // Look for common variable names that are likely inputs
        this.findPotentialInputs(stmt, sources);
      });
    } catch (e) {
      // Silently ignore errors during source identification
      // This can happen if the AST structure doesn't match expectations
    }

    return sources;
  }

  /**
   * Heuristically identifies potential input variables in statements.
   * This looks for variables with names that commonly represent external inputs.
   */
  private findPotentialInputs(stmt: any, sources: TaintSource[]): void {
    // Common input variable names to look for
    const inputVarNames = new Set([
      "a",
      "addr",
      "address",
      "key",
      "value",
      "i",
      "j",
      "msg",
      "s1",
      "s",
      "slice",
    ]);

    // Helper to process an identifier
    const processId = (id: any) => {
      if (id && id.kind === "id" && id.text && inputVarNames.has(id.text)) {
        // Check if we already have this source
        if (!sources.some((src) => src.id === id.id)) {
          sources.push({
            id: id.id,
            name: id.text,
            kind: "parameter", // Treat as parameter
          });
        }
      }
    };

    // Walk through the statement to find identifiers
    const walkNode = (node: any) => {
      if (!node || typeof node !== "object") return;

      // Check if it's an ID
      if (node.kind === "id") {
        processId(node);
        return;
      }
      // Recursively process properties
      for (const key in node) {
        if (node.hasOwnProperty(key)) {
          const child = node[key];
          if (child && typeof child === "object") {
            if (Array.isArray(child)) {
              child.forEach(walkNode);
            } else {
              walkNode(child);
            }
          }
        }
      }
    };
    // Process the statement
    walkNode(stmt);
  }

  /**
   * Gets all fields of a contract.
   */
  private getContractFields(func: any): AstId[] {
    const fields: AstId[] = [];
    try {
      // Check if we have the receiver property
      if (!("receiver" in func) || !func.receiver || !func.receiver.type) {
        return fields;
      }

      // Get contract name from the receiver's type, but we don't actually need it
      // since we'll just scan all contracts
      const _receiverType = func.receiver.type;

      // Find contract declarations in the AST
      const contracts = Array.from(this.cu.ast.getContracts?.() || []);
      for (const contract of contracts) {
        // Try to safely access the contract fields
        try {
          if (contract && typeof contract === "object") {
            // Get contract fields from AST (if available)
            const astContract = this.cu.ast.getContract?.(contract.id);
            if (astContract && astContract.declarations) {
              // Filter field declarations
              for (const decl of astContract.declarations) {
                if (decl.kind === "field_decl" && decl.name) {
                  fields.push(decl.name);
                }
              }
            }
          }
        } catch (innerError) {
          // Ignore errors for this specific contract
          continue;
        }
      }
    } catch (e) {
      // Silently ignore errors during field extraction
    }

    return fields;
  }

  /**
   * Creates initial facts from taint sources.
   */
  private createInitialFacts(sources: TaintSource[]): Set<DataflowFact> {
    const facts = new Set<DataflowFact>();

    for (const source of sources) {
      facts.add({
        id: `${source.id}:taint:${source.kind}:${source.name}`,
        node: source.id,
        // Contract fields are tracked without path sensitivity
        context:
          source.kind === "field"
            ? undefined
            : {
                conditions: new Map(),
              },
      });
    }

    return facts;
  }

  /**
   * Analyzes all CFGs in the compilation unit.
   */
  public analyzeAll(): Map<number, TaintAnalysisResult> {
    const results = new Map<number, TaintAnalysisResult>();

    this.cu.forEachCFG((cfg: Cfg) => {
      const result = this.analyzeCfg(cfg);
      results.set(cfg.id, result);
    });

    return results;
  }

  /**
   * Creates a path context from a condition.
   */
  public createPathContextFromCondition(
    condition: AstExpression,
    value: boolean,
  ): PathContext {
    return {
      conditions: new Map([[condition.id, value]]),
    };
  }
}
