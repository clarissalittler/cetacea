# Browser keyboard and accessibility review

The editor has keyboard skip links before its toolbar. Press Tab from the start
of the page to reach **Skip to proof source**, or Tab again for **Skip to proof
state**. Enter moves focus to that section. Tab leaves the source textarea for
the theorem selector; the editor does not intercept Tab for indentation.
Shift+Tab moves backward through controls.

The source field describes this keyboard behavior. The theorem search field has
an explicit accessible name, **Search theorem names or statements**, independent
of its placeholder. Interactive controls have a visible focus outline; skip
links appear over the toolbar when focused. Proof-state focus uses the same
outline. Existing check/save/assignment statuses expose polite status updates.

## Verified in Chrome on 2026-09-04

Actual Tab and Enter input through browser automation established:

- The first focus target is the source skip link.
- Activating it focuses the source textarea and preserves its contents.
- Tab leaves the textarea for the theorem selector.
- The second skip link focuses the proof-state container.
- The accessibility tree exposes the theorem-search label and editor help.
- A screenshot of the focused skip link shows its text and focus outline.

The updated stylesheet has a versioned URL so an already-open installation
loads these styles on refresh. The browser initially retained the old stylesheet;
verification was repeated with the updated URL.

## Diagnostic navigation and refresh focus

Active-file diagnostics offer a **Go to line N** button. Activating it focuses
the source editor at the end of that line without modifying source. Diagnostics
from other files include their paths and do not offer a misleading jump into
the active file. A project diagnostic whose path exactly matches the active
project root receives the same navigation and source marker as a single file.

The theorem library preserves the focused theorem button when rebuilding its
results. If that entry disappears, focus returns to the search field. Refreshes
while focus is outside the library do not move it. The editor regression harness
checks retained/recovered focus and diagnostic source/line preservation.

## Width and reflow regression

`web/tests/browser-layout.html` loads the actual editor with isolated in-memory
storage, a long project filename and a long theorem name. It expands every help
section and checks document width and control bounds at 320, 768 and 1280 CSS
pixels. The initial 320-pixel run exposed a 1,205-pixel document because native
selectors used their full text width. Labels/selectors now shrink within their
containers and long status/declaration text wraps.

This regression checks horizontal overflow and control reachability, not every
possible proof layout or assistive technology. Source text remains independently
scrollable. The test page never reads or changes saved student work.

## Keyboard error-correction workflow

Verified in Chrome on 2026-09-04 using the 320-pixel isolated editor in
`browser-layout.html`, after its layout assertions completed:

1. Focus the source and enter `theorem practice : True := by` followed by
   `  refl`. The checker reports the line-2 failure.
2. Tab through the theorem selector, tactic, search/scope and expanded help
   summaries to **Go to line 2**. This took 13 Tab presses in this fixture.
3. Press Enter. Focus returns to the source at the error line.
4. Use Home, Shift+End and typing to replace the line with `  trivial`.
5. The checker reports **HOL certified**, removes diagnostics, and displays the
   completed explanation. Focus remains in the source editor.

Only the initial source focus used a pointer action; navigation from the failing
proof through its diagnostic and correction used actual keyboard input. The
fixture uses in-memory storage, so normal student source was untouched.

## Keyboard theorem search and insertion

In the isolated narrow editor, enter a completed `helper : True` theorem and an
unfinished `practice : True := by` header, leaving the caret at that header.
Actual keyboard verification on 2026-09-04 used Tab to reach theorem search,
typed `helper`, then used Tab through the scope selector to the matching theorem
button and Enter to insert it. The editor retained the saved source position,
inserted `apply helper` after that line, and restored source focus.

This exposed inconsistent generated indentation. Insertions now add two spaces
after a proof header or case-branch header, retain existing tactic indentation,
and follow the preceding proof line when starting from an empty line. Unit tests
cover these contexts; the editor harness checks the exact inserted source,
restored focus and resulting proof certification.

## Remaining verification

This is an initial keyboard pass, not a completed accessibility audit. Exercise
the assignment file selection flow entirely by keyboard. Error
correction, theorem search and insertion are verified as described above. Check focus retention during asynchronous updates,
narrow screens and zoom, and test announcements with an actual screen reader.
The existing editor recovery harness covers assignment correctness and source
preservation, but its scripted clicks do not establish keyboard usability.

## Assignment clearing and checkpoint recovery

Verified in Chrome on 2026-09-04 at 320 pixels using
`browser-layout.html?assignment=1`. This optional fixture seeds an assignment
in isolated in-memory storage. After initial focus through the source skip
link, Shift+Tab reaches **Clear assignment** and Enter clears it. Clearing
preserves a checkpoint containing the selected assignment and source.

The initial run lost focus because the clear button disabled itself. The
handler now moves focus to **Open assignment** when the clear button was
focused. Keyboard navigation then reaches **Saved checkpoints**; Down selects
the saved entry, Tab reaches **Restore checkpoint**, and Enter restores it.
The assignment is rechecked, reports **Assignment satisfied**, retains the
source, and leaves focus on Restore checkpoint. No pointer was used between
source focus and completed recovery.

The embedded fixture also exposed a skip-link issue: its base URL caused
native fragment navigation to replace the isolated editor with another page.
Skip links now explicitly focus and scroll their local targets without
navigation. The browser regression harness covers both targets and source
preservation under an embedding base URL.
All 25 browser recovery checks and the JavaScript test files passed after
these focus changes.

The Open assignment keyboard control reached a file chooser, but the Chrome
extension rejected setting its local test file (`Not allowed`). File selection
through that chooser was not verified. This is separate from the tested archive
parser, scripted import flow and native/browser grading parity. A screen-reader
pass and complete keyboard file selection remain open.
