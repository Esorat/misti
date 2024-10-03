import { CompilationUnit } from "../../internals/ir";
import {
  foldStatements,
  collectMutations,
  mutationNames,
  funName,
} from "../../internals/tact";
import { intersection } from "../../internals/util";
import { MistiTactWarning, Severity } from "../../internals/warnings";
import { ASTDetector } from "../detector";
import {
  AstStatement,
  AstFunctionDef,
  AstContractInit,
  idText,
} from "@tact-lang/compiler/dist/grammar/ast";

/**
 * A detector that highlights cases where function argument mutations are ineffective
 * due to [call-by-value semantics](https://en.wikipedia.org/wiki/Evaluation_strategy#Call_by_value) in Tact.
 *
 * ## Why is it bad?
 * In Tact, function arguments are passed by value, meaning that any mutations applied
 * to these arguments will only affect the local copy of the variable within the function.
 * Such mutations are unobservable outside the function, except for potentially
 * increasing gas consumption or causing exceptions.
 *
 * ## Example
 * ```tact
 * fun addEntry(m: map<Int,Int>) {
 *   m.set(1, 10); // Bad: Mutating the copy
 * }
 * ```
 *
 * Use instead:
 * ```tact
 * fun addEntry() {
 *   self.m.set(1, 10); // OK: Changing contract's state
 * }
 * ```
 *
 * Alternatively, you could redesign the method:
 * ```tact
 * fun generateNewValue(): Int {
 *   // ... produce new value for the map
 *   return self.nextValue + 1;
 * }
 *
 * m.set(self.nextKey, self.generateNewValue()); // OK
 * ```
 */
export class ArgCopyMutation extends ASTDetector {
  severity = Severity.HIGH;

  async check(cu: CompilationUnit): Promise<MistiTactWarning[]> {
    return Array.from(cu.ast.getFunctions()).reduce((acc, fun) => {
      if (fun.kind === "contract_init" || fun.kind === "function_def") {
        const mutations = foldStatements(
          fun,
          new Map<string, AstStatement[]>(),
          (acc, stmt) => {
            const interestingArgs = this.collectInterestingArgs(fun);
            if (interestingArgs.length === 0) {
              return acc;
            }
            const stmtMutations = this.findArgCopyMutations(
              stmt,
              interestingArgs,
            );
            return Array.from(stmtMutations.entries()).reduce(
              (newAcc, [argName, mutationStmts]) => {
                const existingStmts = newAcc.get(argName) || [];
                return newAcc.set(argName, [
                  ...existingStmts,
                  ...mutationStmts,
                ]);
              },
              new Map(acc),
            );
          },
        );
        Array.from(mutations.keys()).forEach((argName) => {
          const argMutationStatements = mutations.get(argName)!;
          const occurrencesStr =
            argMutationStatements.length > 1
              ? ` (${argMutationStatements.length} more times)`
              : "";
          acc.push(
            this.makeWarning(
              `Function ${funName(fun)} argument ${argName} is mutated${occurrencesStr}`,
              argMutationStatements[0].loc,
              {
                extraDescription:
                  "Mutating function arguments has no effect outside the function due to call-by-value semantics",
                suggestion:
                  "Return the modified value or use the contract's state to avoid unnecessary mutations",
              },
            ),
          );
        });
        return acc.concat();
      }
      return acc;
    }, [] as MistiTactWarning[]);
  }

  /**
   * Collects names of function argument that should be handled by this detector.
   */
  private collectInterestingArgs(
    fun: AstFunctionDef | AstContractInit,
  ): string[] {
    return fun.params.reduce((acc, p) => {
      // TODO: Should be improved when we have types in AST
      // Sort out integral types. It is unlikely that the user will expect they change inside the function.
      // See: tact:src/types/resolveExpression.ts
      const skipTypes = ["Int", "Bool"];
      if (p.type.kind === "type_id" && skipTypes.includes(p.type.text)) {
        return acc;
      }
      acc.push(idText(p.name));
      return acc;
    }, [] as string[]);
  }

  /**
   * Identifies mutations of function arguments within a given statement.
   * @param argNames Names of function arguments to check for mutations.
   * @returns A map of argument names to the statements where they are mutated.
   */
  private findArgCopyMutations(
    stmt: AstStatement,
    argNames: string[],
  ): Map<string, AstStatement[]> {
    const mutations = collectMutations(stmt);
    const foundMutations = mutations
      ? intersection(argNames, mutationNames(mutations.mutatedLocals))
      : [];
    return foundMutations.reduce((mutationMap, argName) => {
      const existingStatements = mutationMap.get(argName) || [];
      return mutationMap.set(argName, [...existingStatements, stmt]);
    }, new Map<string, AstStatement[]>());
  }
}
