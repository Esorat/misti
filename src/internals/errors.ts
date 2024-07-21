import { ASTRef } from "@tact-lang/compiler/dist/grammar/ast";
import * as path from "path";

/**
 * Enumerates the levels of severity that can be assigned to detected findings.
 */
export enum Severity {
  INFO,
  LOW,
  MEDIUM,
  HIGH,
  CRITICAL,
}

/**
 * Error instance that refers to a specific place in a Tact contract.
 */
export class MistiTactError extends Error {
  readonly ref: ASTRef;
  constructor(
    msg: string,
    ref: ASTRef,
    private _severity: Severity,
  ) {
    super(msg);
    this.ref = ref;
  }

  /**
   * Gets the severity level of this error.
   * @returns The severity as defined by the Severity enum.
   */
  get severity(): Severity {
    return this._severity;
  }
}

/**
 * Constructs an error object with a description and the source code location.
 *
 * @param description Descriptive text of the error.
 * @param severity Severity of the finding.
 * @param ref Reference to the source code that includes file information and position data.
 * @param extraDescription More comprehensive description that clarifies the error in a greater detail
 * @param docURL URL to the lint documentation
 * @param suggestion Suggested change in the source code
 * @returns A new MistiTactError containing the error message and source code reference.
 */
export function createError(
  description: string,
  severity: Severity,
  ref: ASTRef,
  data: Partial<{
    extraDescription: string;
    docURL: string;
    suggestion: string;
  }> = {},
): MistiTactError {
  const {
    extraDescription = undefined,
    docURL = undefined,
    suggestion = undefined,
  } = data;
  const pos = ref.file
    ? (() => {
        const lc = ref.interval.getLineAndColumn() as {
          lineNum: number;
          colNum: number;
        };
        const lcStr = `${lc}`;
        const lcLines = lcStr.split("\n");
        lcLines.shift();
        const relativeFilePath = path.relative(process.cwd(), ref.file);
        return `${relativeFilePath}:${lc.lineNum}:${lc.colNum}:\n${lcLines.join("\n")}`;
      })()
    : "";
  const docURLStr = docURL === undefined ? "" : `(see: ${docURL})`;
  const extraDescriptionStr =
    extraDescription === undefined ? "" : `\n${extraDescription}`;
  const suggestionStr =
    suggestion === undefined ? "" : `\nSuggestion: ${suggestion}`;
  const msg = `${pos}${description}${docURLStr}${extraDescriptionStr}${suggestionStr}`;
  return new MistiTactError(msg, ref, severity);
}
