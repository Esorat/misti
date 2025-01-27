import { CompilationUnit } from "../../internals/ir";
import { foldStatements, evalExpr } from "../../internals/tact";
import { MistiTactWarning, Severity } from "../../internals/warnings";
import { AstDetector } from "../detector";
import {
  AstStatement,
  AstExpression,
} from "@tact-lang/compiler/dist/grammar/ast";

/**
 * An optional detector that identifies potentially problematic loops, such as those
 * with unbounded conditions or excessive iteration counts.
 *
 * ## Why is it bad?
 * Loops with always-true conditions or massive iteration limits can lead to high
 * gas consumption and even denial of service (DoS) issues. By flagging these loops,
 * this detector aids auditors in catching potential performance or security risks.
 *
 * ## Example
 * ```tact
 * repeat (1_000_001) { // Highlighted by detector as high iteration count
 *     // ...
 * }
 *
 * while (true) { // Highlighted as unbounded condition
 *     // ...
 * }
 * ```
 */
export class SuspiciousLoop extends AstDetector {
  severity = Severity.HIGH;

  async check(cu: CompilationUnit): Promise<MistiTactWarning[]> {
    const processedLoopIds = new Set<number>();
    return Array.from(cu.ast.getProgramEntries()).reduce((acc, node) => {
      return acc.concat(
        ...foldStatements(
          node,
          (acc, stmt) => {
            return acc.concat(
              this.analyzeLoopStatement(stmt, processedLoopIds),
            );
          },
          acc,
          { flatStmts: true },
        ),
      );
    }, [] as MistiTactWarning[]);
  }

  /**
   * Analyzes a loop statement to determine if it contains a suspicious condition.
   * @param stmt - The statement to analyze.
   * @param processedLoopIds - A set of loop IDs already processed.
   * @returns An array of MistiTactWarning objects if a suspicious loop is detected.
   */
  private analyzeLoopStatement(
    stmt: AstStatement,
    processedLoopIds: Set<number>,
  ): MistiTactWarning[] {
    if (processedLoopIds.has(stmt.id)) {
      return [];
    }
    processedLoopIds.add(stmt.id);
    let warnings: MistiTactWarning[] = [];
    if ("statements" in stmt) {
      for (const nestedStmt of stmt.statements) {
        warnings = warnings.concat(
          this.analyzeLoopStatement(nestedStmt, processedLoopIds),
        );
      }
    }
    if (stmt.kind === "statement_repeat") {
      warnings = warnings.concat(this.isBig(stmt.iterations));
    }
    if (stmt.kind === "statement_while") {
      const bodyCount = "statements" in stmt ? stmt.statements.length : 0;
      warnings = warnings.concat(
        this.checkWhileLoopCondition(stmt.condition, bodyCount),
      );
    }
    return warnings;
  }

  /**
   * Checks if an integer expression evaluates to a large number (>= 1_000_000).
   * Used only in `repeat(...)`.
   */
  private isBig(expr: AstExpression): MistiTactWarning[] {
    const result = evalExpr(expr);
    if (
      result !== undefined &&
      typeof result === "bigint" &&
      result >= BigInt(1_000_000)
    ) {
      return [
        this.makeWarning("Potential high-cost loop", expr.loc, {
          suggestion: "Avoid excessive iterations in loops",
        }),
      ];
    }
    return [];
  }

  /**
   * Checks a `while` loop condition for:
   * - Always true ( => "Potential infinite loop")
   * - Always false ( => "Loop condition is always false" if loop body has > 0 statements)
   */
  private checkWhileLoopCondition(
    expr: AstExpression,
    bodyCount: number,
  ): MistiTactWarning[] {
    const result = evalExpr(expr);
    if (result !== undefined && typeof result === "boolean") {
      if (result === true) {
        return [
          this.makeWarning("Potential infinite loop", expr.loc, {
            suggestion: "Avoid unbounded conditions in loops",
          }),
        ];
      }
      if (result === false && bodyCount > 0) {
        return [
          this.makeWarning("Loop condition is always false", expr.loc, {
            suggestion:
              "The condition is always false; therefore, the body will never execute",
          }),
        ];
      }
    }
    return [];
  }
}
