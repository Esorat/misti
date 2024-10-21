import { ToolConfig, OutputFormat } from "./types";
import { Severity, parseSeverity } from "../internals/warnings";
import { Option } from "commander";

export const STDOUT_PATH = "-";

export interface CLIOptions {
  tools: ToolConfig[] | undefined;
  outputPath: string;
  listTools: boolean;
  outputFormat: OutputFormat;
  colors: boolean;
  soufflePath: string;
  souffleBinary: string;
  souffleVerbose: boolean;
  tactStdlibPath: string | undefined;
  verbose: boolean;
  quiet: boolean;
  minSeverity: Severity;
  enabledDetectors: string[] | undefined;
  disabledDetectors: string[] | undefined;
  allDetectors: boolean;
  config: string | undefined;
  newDetector: string | undefined;
  listDetectors: boolean;
}

export const cliOptionDefaults: Required<CLIOptions> = {
  tools: undefined,
  outputPath: STDOUT_PATH,
  listTools: false,
  outputFormat: "plain",
  colors: true, // Default: colors enabled
  soufflePath: "/tmp/misti/souffle",
  souffleBinary: "souffle",
  souffleVerbose: false,
  tactStdlibPath: undefined,
  verbose: false,
  quiet: false,
  minSeverity: Severity.INFO,
  enabledDetectors: undefined,
  disabledDetectors: undefined,
  allDetectors: false,
  config: undefined,
  newDetector: undefined,
  listDetectors: false,
};

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
    .default(cliOptionDefaults.tools),
  new Option(
    "--output-path <PATH>",
    [
      "Directory to save warnings or output generated by tools.",
      `If <PATH> is ${STDOUT_PATH}, then stdout is used.`,
    ].join(" "),
  ).default(cliOptionDefaults.outputPath),
  new Option("--list-tools", "List available tools and their options.").default(
    cliOptionDefaults.listTools,
  ),
  new Option(
    "-o, --output-format <json|plain>",
    "Set the output format for all tools and warnings",
  ).default(cliOptionDefaults.outputFormat),
  new Option("-C, --no-colors", "Disables ANSI colors in the output.").default(
    cliOptionDefaults.colors, // Invert because the option is --no-colors
  ),
  new Option("--souffle-binary <PATH>", "Path to the Soufflé binary.").default(
    cliOptionDefaults.souffleBinary,
  ),
  new Option(
    "--souffle-path <PATH>",
    "Directory to save generated Soufflé files.",
  ).default(cliOptionDefaults.soufflePath),
  new Option(
    "--souffle-verbose",
    "Generate human-readable, but more verbose, Soufflé files.",
  ).default(cliOptionDefaults.souffleVerbose),
  new Option(
    "--tact-stdlib-path <PATH>",
    "Path to the Tact standard library.",
  ).default(cliOptionDefaults.tactStdlibPath),
  new Option("-v, --verbose", "Enable verbose output.").default(
    cliOptionDefaults.verbose,
  ),
  new Option("-q, --quiet", "Suppress output.").default(
    cliOptionDefaults.quiet,
  ),
  new Option(
    "-m, --min-severity <info|low|medium|high|critical>",
    "Minimum level of severity to report.",
  ),
  new Option("--list-detectors", "List available built-in detectors.").default(
    cliOptionDefaults.listDetectors,
  )
    .default(Severity.INFO)
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
    .default(cliOptionDefaults.enabledDetectors),
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
    .default(cliOptionDefaults.disabledDetectors),
  new Option(
    "-A, --all-detectors",
    "Enable all the available built-in detectors.",
  ).default(cliOptionDefaults.allDetectors),
  new Option(
    "-c, --config <PATH>",
    "Path to the Misti configuration file.",
  ).default(cliOptionDefaults.config),
  new Option("--new-detector <PATH>", "Creates a new custom detector.").default(
    cliOptionDefaults.newDetector,
  ),
];
