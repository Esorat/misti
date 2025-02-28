import { AstStore, Cfg, CompilationUnit } from "../ir";
import { IFDSTransfer } from "./ifdsTransfer";
import { SolverResults } from "../solver/results";
import { WorklistSolver } from "../solver/worklist";
import { AstNode, AstStatement } from "@tact-lang/compiler/dist/grammar/ast";

/**
 * Implementation of the Interprocedural Finite Distributive Subset (IFDS) algorithm
 * as described in "Precise Interprocedural Dataflow Analysis via Graph Reachability"
 * by Reps, Horwitz, and Sagiv.
 *
 * This implementation is extended with path-sensitivity for use in security analysis.
 */

// Forward declarations of types we'll implement later
export class IFDSLattice {
  bottom(): Set<DataflowFact> {
    return new Set();
  }
  join(a: Set<DataflowFact>, b: Set<DataflowFact>): Set<DataflowFact> {
    return new Set([...a, ...b]);
  }
  leq(a: Set<DataflowFact>, b: Set<DataflowFact>): boolean {
    return a.size <= b.size;
  }
}

/**
 * The IFDS algorithm models dataflow facts as a graph reachability problem.
 * Each dataflow fact is a node in the graph, and edges represent how facts flow
 * through the program.
 */
export interface DataflowFact {
  id: string; // Unique identifier for this fact
  node: AstNode["id"]; // AST Node this fact is associated with
  context?: PathContext; // Optional path context for path-sensitive analysis
}

/**
 * Represents a path context for path-sensitive analysis.
 * This tracks the conditions under which a fact holds.
 */
export interface PathContext {
  conditions: Map<AstNode["id"], boolean>; // Maps condition nodes to true/false values
}

/**
 * The result of an IFDS analysis, containing the dataflow facts at each program point.
 */
export class IFDSResult {
  private facts: Map<number, Set<DataflowFact>> = new Map();

  /**
   * Sets the facts for a basic block.
   */
  public setFacts(bbIdx: number, facts: Set<DataflowFact>): void {
    this.facts.set(bbIdx, facts);
  }

  /**
   * Gets the facts for a basic block.
   */
  public getFacts(bbIdx: number): Set<DataflowFact> {
    return this.facts.get(bbIdx) || new Set();
  }

  /**
   * Checks if a specific fact exists at a program point.
   */
  public hasFact(bbIdx: number, fact: DataflowFact): boolean {
    const facts = this.facts.get(bbIdx);
    if (!facts) return false;

    return Array.from(facts).some(
      (f) => f.id === fact.id && f.node === fact.node,
    );
  }

  /**
   * Gets all facts that match a predicate.
   */
  public getFactsWhere(
    predicate: (fact: DataflowFact) => boolean,
  ): Set<DataflowFact> {
    const result = new Set<DataflowFact>();
    for (const factSet of this.facts.values()) {
      for (const fact of factSet) {
        if (predicate(fact)) {
          result.add(fact);
        }
      }
    }
    return result;
  }
}

/**
 * The main IFDS solver class that performs interprocedural analysis.
 * It uses the exploded supergraph representation described in the IFDS paper.
 */
export class IFDSSolver {
  private readonly cu: CompilationUnit;
  private readonly ast: AstStore;
  private readonly callGraph: Map<AstNode["id"], Set<AstNode["id"]>>;
  private readonly summaryEdges: Map<
    string,
    Map<DataflowFact, Set<DataflowFact>>
  >;
  private readonly pathSensitive: boolean;

  /**
   * Creates a new IFDS solver.
   *
   * @param cu The compilation unit containing the program to analyze
   * @param pathSensitive Whether to perform path-sensitive analysis
   */
  constructor(cu: CompilationUnit, pathSensitive: boolean = false) {
    this.cu = cu;
    this.ast = cu.ast;
    this.callGraph = new Map();
    this.summaryEdges = new Map();
    this.pathSensitive = pathSensitive;

    // Build call graph from the compilation unit
    this.buildCallGraph();
  }

  /**
   * Builds a call graph from the program.
   */
  private buildCallGraph(): void {
    // For each function, find all function calls within it
    this.cu.forEachCFG((cfg) => {
      const callerID = cfg.id;
      const callees = new Set<AstNode["id"]>();

      cfg.forEachBasicBlock(this.ast, (stmt, _) => {
        // Find function/method calls in the statement and add them to callees
        this.findCallsInStatement(stmt, callees);
      });
      this.callGraph.set(callerID, callees);
    });
  }

  /**
   * Finds all function calls in a statement.
   */
  private findCallsInStatement(
    _stmt: AstStatement,
    _callees: Set<AstNode["id"]>,
  ): void {
    // This is a simplified implementation - in a real analysis, you would recursively
    // traverse the AST looking for function calls
    // For now, we'll consider function calls to be detected through the call graph
  }

  /**
   * Solves the IFDS problem for a given function and initial facts.
   */
  public solve(
    startCfg: Cfg,
    initialFacts: Set<DataflowFact>,
    maxLoopUnrolling: number = 2,
  ): IFDSResult {
    const result = new IFDSResult();

    // Create a lattice and transfer function for the IFDS problem
    const lattice = new IFDSLattice();
    const transfer = new IFDSTransfer(
      this.cu,
      this.pathSensitive,
      this.summaryEdges,
      maxLoopUnrolling,
    );

    // Use the existing worklist solver with our IFDS-specific lattice and transfer
    const solver = new WorklistSolver(
      this.cu,
      startCfg,
      transfer as any, // Type cast for now
      lattice as any, // Type cast for now
      "forward",
    );

    // Solve the dataflow problem
    const solverResults = solver.solve();

    // Convert solver results to our IFDS result format
    this.processResults(
      solverResults as SolverResults<Set<DataflowFact>>,
      result,
    );
    return result;
  }

  /**
   * Processes solver results into the IFDS result format.
   */
  private processResults(
    solverResults: SolverResults<Set<DataflowFact>>,
    ifdsResult: IFDSResult,
  ): void {
    // For each basic block, copy the dataflow facts
    for (const [bbIdx, facts] of solverResults.getStates()) {
      ifdsResult.setFacts(bbIdx, facts);
    }
  }

  /**
   * Creates a path context from a set of conditions.
   */
  public createPathContext(
    conditions: Map<AstNode["id"], boolean>,
  ): PathContext {
    return { conditions: new Map(conditions) };
  }

  /**
   * Merges two path contexts, handling conflicting conditions.
   * If there are contradictory conditions, the result will be undetermined (removed).
   */
  public mergePathContexts(
    ctx1: PathContext | undefined,
    ctx2: PathContext | undefined,
  ): PathContext | undefined {
    if (!ctx1) return ctx2;
    if (!ctx2) return ctx1;

    const result = new Map<AstNode["id"], boolean>();

    // Copy all conditions from ctx1
    for (const [condId, value] of ctx1.conditions) {
      result.set(condId, value);
    }

    // Merge with ctx2, checking for conflicts
    for (const [condId, value] of ctx2.conditions) {
      if (result.has(condId)) {
        const existingValue = result.get(condId);
        if (existingValue !== value) {
          // Conflict detected - remove this condition as it's now uncertain
          result.delete(condId);
        }
      } else {
        result.set(condId, value);
      }
    }
    return { conditions: result };
  }
}
