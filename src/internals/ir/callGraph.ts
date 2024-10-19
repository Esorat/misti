import { unreachable } from "../util";
import { TactASTStore } from "./astStore";
import { IdxGenerator } from "./indices";
import {
  AstFunctionDef,
  AstReceiver,
  AstContractInit,
  AstStatement,
  AstStaticCall,
  AstMethodCall,
  AstExpression,
  AstStructFieldInitializer,
} from "@tact-lang/compiler/dist/grammar/ast";

export class CGEdge {
  public idx: number;
  constructor(
    public src: number,
    public dst: number,
  ) {
    this.idx = IdxGenerator.next("cg_edge");
  }
}

export class CGNode {
  public idx: number;
  public inEdges: Set<number> = new Set();
  public outEdges: Set<number> = new Set();
  constructor(
    public astId: number,
    public name: string,
  ) {
    this.idx = IdxGenerator.next("cg_node");
  }
}

export class CallGraph {
  private nodeMap: Map<number, CGNode> = new Map();
  private edgesMap: Map<number, CGEdge> = new Map();
  public getNodes(): Map<number, CGNode> {
    return this.nodeMap;
  }
  public getEdges(): Map<number, CGEdge> {
    return this.edgesMap;
  }
  build(astStore: TactASTStore): CallGraph {
    this.addFunctionsToNodes(astStore);
    this.analyzeFunctionCalls(astStore);
    return this;
  }

  private addFunctionsToNodes(astStore: TactASTStore) {
    for (const func of astStore.getFunctions()) {
      const funcName = this.getFunctionName(func);
      if (funcName) {
        const node = new CGNode(func.id, funcName);
        this.nodeMap.set(func.id, node);
      }
    }
  }

  private analyzeFunctionCalls(astStore: TactASTStore) {
    for (const func of astStore.getFunctions()) {
      const funcName = this.getFunctionName(func);
      if (funcName) {
        this.processStatements(func.statements, func.id);
      }
    }
  }

  private getFunctionName(
    func: AstFunctionDef | AstReceiver | AstContractInit,
  ): string | undefined {
    switch (func.kind) {
      case "function_def":
        return func.name.text;
      case "contract_init":
        return `contract_init_${func.id}`;
      case "receiver":
        return `receiver_${func.id}`;
      default:
        unreachable(func);
    }
  }

  private processStatements(statements: AstStatement[], callerId: number) {
    for (const stmt of statements) {
      switch (stmt.kind) {
        case "statement_expression":
          this.processExpression(stmt.expression, callerId);
          break;
        case "statement_condition":
          this.processStatements(stmt.trueStatements, callerId);
          if (stmt.falseStatements) {
            this.processStatements(stmt.falseStatements, callerId);
          }
          break;
        case "statement_while":
        case "statement_until":
        case "statement_repeat":
        case "statement_foreach":
          this.processStatements(stmt.statements, callerId);
          break;
        case "statement_try":
          this.processStatements(stmt.statements, callerId);
          break;
        case "statement_try_catch":
          this.processStatements(stmt.statements, callerId);
          this.processStatements(stmt.catchStatements, callerId);
          break;
        case "statement_let":
        case "statement_return":
        case "statement_assign":
        case "statement_augmentedassign":
          if (stmt.expression) {
            this.processExpression(stmt.expression, callerId);
          }
          break;
        default:
          console.warn(`Unhandled statement type: ${(stmt as any).kind}`, stmt);
      }
    }
  }

  private processExpression(
    expr: AstExpression | AstStructFieldInitializer,
    callerId: number,
  ) {
    this.forEachExpression(expr, (nestedExpr) => {
      let calleeId: number | undefined;
      if (nestedExpr.kind === "static_call") {
        const staticCall = nestedExpr as AstStaticCall;
        calleeId = this.findOrAddFunction(staticCall.function.text);
      } else if (nestedExpr.kind === "method_call") {
        const methodCall = nestedExpr as AstMethodCall;
        calleeId = this.findOrAddFunction(methodCall.method.text);
      }
      if (calleeId !== undefined) {
        this.addEdge(callerId, calleeId);
      }
    });
  }

  private forEachExpression(
    expr: AstExpression | AstStructFieldInitializer,
    callback: (expr: AstExpression) => void,
  ) {
    if (expr.kind !== "struct_field_initializer") {
      callback(expr as AstExpression);
    }

    switch (expr.kind) {
      case "static_call":
      case "method_call": {
        const callExpr = expr as AstStaticCall | AstMethodCall;
        for (const arg of callExpr.args) {
          this.forEachExpression(arg, callback);
        }
        break;
      }
      default:
        break;
    }
  }

  private findOrAddFunction(name: string): number {
    const existingNode = Array.from(this.nodeMap.values()).find(
      (node: CGNode) => node.name === name,
    );
    if (existingNode) {
      return existingNode.astId;
    }
    const newNode = new CGNode(IdxGenerator.next("cg_node"), name);
    this.nodeMap.set(newNode.astId, newNode);
    return newNode.astId;
  }

  private addEdge(src: number, dst: number) {
    const srcNode = this.nodeMap.get(src);
    const dstNode = this.nodeMap.get(dst);
    if (srcNode && dstNode) {
      const edge = new CGEdge(src, dst);
      this.edgesMap.set(edge.idx, edge);
      srcNode.outEdges.add(edge.idx);
      dstNode.inEdges.add(edge.idx);
    }
  }

  areConnected(src: number, dst: number): boolean {
    const srcNode = this.nodeMap.get(src);
    const dstNode = this.nodeMap.get(dst);
    if (!srcNode || !dstNode) {
      return false;
    }
    const queue: number[] = [src];
    const visited = new Set<number>([src]);

    while (queue.length > 0) {
      const current = queue.shift()!;

      if (current === dst) {
        return true;
      }
      const currentNode = this.nodeMap.get(current);
      if (currentNode) {
        for (const edgeId of currentNode.outEdges) {
          const edge = this.edgesMap.get(edgeId);
          if (edge && !visited.has(edge.dst)) {
            visited.add(edge.dst);
            queue.push(edge.dst);
          }
        }
      }
    }
    return false;
  }
}
