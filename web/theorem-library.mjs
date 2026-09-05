// Receipt identity distinguishes aliases of one declaration from distinct
// theorems that happen to state the same proposition. Never group local work.
export function libraryEntries(theorems, query = '', scope = 'all', suggested = new Set()) {
  query = query.trim().toLowerCase();
  const groups = new Map();
  for (const theorem of theorems) {
    if (scope === 'imported' && !theorem.is_imported) continue;
    if (scope === 'local' && theorem.is_imported) continue;
    const key = theorem.is_imported && theorem.receipt_id != null
      ? `receipt:${theorem.receipt_id}` : theorem;
    if (!groups.has(key)) groups.set(key, []);
    groups.get(key).push(theorem);
  }
  return [...groups.values()].flatMap(aliases => {
    const matching = aliases.filter(t => !query || t.name.toLowerCase().includes(query) || (t.statement ?? '').toLowerCase().includes(query));
    if (!matching.length) return [];
    // If an alias is named in the query, keep that exact spelling usable.
    const preferred = matching.find(t => query && t.name.toLowerCase().includes(query))
      ?? matching.find(t => suggested.has(t.name)) ?? matching[0];
    return [{ ...preferred, aliases: aliases.map(t => t.name), suggested: aliases.some(t => suggested.has(t.name)) }];
  }).sort((a, b) => Number(b.suggested) - Number(a.suggested)
    || Number(a.is_imported) - Number(b.is_imported) || a.name.localeCompare(b.name));
}
