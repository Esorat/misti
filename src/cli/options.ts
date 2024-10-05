import { ToolConfig, OutputFormat } from "./types";
import { Severity, parseSeverity } from "../internals/warnings";
import { Option } from "commander";

export interface CLIOptions {
  tools?: ToolConfig[];
  outputPath?: string;
  listTools?: boolean;
  outputFormat?: OutputFormat;
  colors?: boolean;
  soufflePath?: string;
  souffleBinary?: string;
  souffleVerbose?: boolean;
  tactStdlibPath?: string;
  verbose?: boolean;
  quiet?: boolean;
  minSeverity?: Severity;
  enabledDetectors?: string[];
  disabledDetectors?: string[];
  allDetectors?: boolean;
  config?: string;
}

export const cliOptions = [
  new Option(
    "-t, --tools <className[:key=value...]>",
    "Specify a tool to enable with optional configuration. Can be used multiple times.",
  )
    .argParser((value, previous: ToolConfig[] = []) => {
      const [className, ...optionParts] = value.split(":");
      const options: Record<string, unknown> = {};
      optionParts.forEach((part) => {
        const [key, val] = part.split("=");
        options[key] = val;
      });
      const toolConfig = { className, options };
      return previous.concat([toolConfig]);
    })
    .default(undefined),
  new Option(
    "--output-path <PATH>",
    "Directory to save warnings or output generated by tools. If <PATH> is '-', then stdout is used.",
  ).default(undefined),
  new Option("--list-tools", "List available tools and their options.").default(
    false,
  ),
  new Option(
    "-o, --output-format <json|plain>",
    "Set the output format for all tools and warnings",
  ).default(undefined),
  new Option("-C, --no-colors", "Disables ANSI colors in the output.").default(
    undefined,
  ),
  new Option("--souffle-binary <PATH>", "Path to the Soufflé binary.").default(
    "souffle",
  ),
  new Option(
    "--souffle-path <PATH>",
    "Directory to save generated Soufflé files.",
  ).default("/tmp/misti/souffle"),
  new Option(
    "--souffle-verbose",
    "Generate human-readable, but more verbose, Soufflé files.",
  ).default(false),
  new Option("--tact-stdlib-path <PATH>", "Path to the Tact standard library."),
  new Option("-v, --verbose", "Enable verbose output.").default(false),
  new Option("-q, --quiet", "Suppress output.").default(false),
  new Option(
    "-m, --min-severity <info|low|medium|high|critical>",
    "Minimum level of severity to report.",
  )
    .default(undefined)
    .argParser(parseSeverity),
  new Option(
    "-de, --enabled-detectors <name|path:name>",
    "A comma-separated list of detectors to enable.",
  )
    .argParser((value) => {
      const detectors = value.split(",").map((detector) => detector.trim());
      if (detectors.length === 0) {
        throw new Error(
          "The --enabled-detectors option requires a non-empty list of detector names.",
        );
      }
      return detectors;
    })
    .default(undefined),
  new Option(
    "-dd, --disabled-detectors <names>",
    "A comma-separated list of names of detectors to disable.",
  )
    .argParser((value) => {
      const detectors = value.split(",").map((detector) => detector.trim());
      if (detectors.length === 0) {
        throw new Error(
          "The --disabled-detectors option requires a non-empty list of detector names.",
        );
      }
      return detectors;
    })
    .default(undefined),
  new Option(
    "-A, --all-detectors",
    "Enable all the available built-in detectors.",
  ).default(false),
  new Option("-c, --config <PATH>", "Path to the Misti configuration file."),
  new Option("--new-detector <PATH>", "Creates a new custom detector.").default(
    undefined,
  ),
];
