"""Parse and display the Ultra pipeline cost model explanation."""

import re
from lean_driver import GeneratedProgram


def extract_ultra_report(source: str) -> str:
    """Extract the Ultra report from the C/Rust source header comment.

    The generated code starts with a block comment containing the report:
    /* TRZK Ultra NTT Benchmark
     * Field: BabyBear (p = 2013265921)
     * Pipeline: Ultra (Ruler + bounds + colored + verified codegen)
     *    === Truth Ultra Report ===
     *    ...
     */
    """
    # Find the header comment block
    m = re.search(r'/\*.*?Ultra.*?\*/', source, re.DOTALL)
    if not m:
        # Try Rust-style comments
        lines = []
        for line in source.split('\n'):
            if line.startswith('//'):
                lines.append(line.lstrip('/ '))
            elif lines:
                break
        if lines:
            return '\n'.join(lines)
        return "(no Ultra report found in source)"

    # Clean up: remove leading " * " from each line
    raw = m.group(0)
    cleaned = []
    for line in raw.split('\n'):
        line = line.strip()
        line = re.sub(r'^\s*/?\*+\s?', '', line)
        line = re.sub(r'\s*\*/$', '', line)
        if line:
            cleaned.append(line)
    return '\n'.join(cleaned)


def format_explanation(program: GeneratedProgram) -> str:
    """Format the cost model explanation for display."""
    report = extract_ultra_report(program.source)
    return (
        f"=== Cost Model Explanation: {program.field} N=2^{program.log_n} "
        f"({program.hardware}) ===\n{report}\n"
    )
