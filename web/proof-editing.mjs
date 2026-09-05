// Describe an insertion without changing source or the editor's selection.
export function tacticInsertion(source, cursor, tactic) {
  const start = Math.max(0, Math.min(cursor, source.length));
  const lineStart = source.lastIndexOf('\n', start - 1) + 1;
  const nextNewline = source.indexOf('\n', start);
  const offset = nextNewline === -1 ? source.length : nextNewline;
  let context = source.slice(lineStart, offset);
  // On an empty, unindented line, follow the preceding proof line's layout.
  if (!context.trim() && !context.length) {
    context = source.slice(0, lineStart).split('\n').findLast(line => line.trim()) ?? '';
  }
  let indent = context.match(/^[ \t]*/)[0];
  if (/:=\s*by\s*(?:--.*)?$/.test(context) || /^\s*\|.*=>\s*(?:--.*)?$/.test(context)) indent += '  ';
  return {offset, text: `\n${indent}${tactic}`};
}
