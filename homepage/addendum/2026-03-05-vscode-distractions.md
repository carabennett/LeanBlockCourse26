---
title: "Disabling VS Code distractions"
parent: Addendum
nav_order: 9995
---

# Disabling VS Code distractions
{: .no_toc }

*March 5, 2026*

---

VS Code ships with several features that actively interfere when writing Lean: Copilot suggestions overwrite tactic completions, the formatter mangles whitespace in proofs, and word-based autocomplete clutters the suggestion list. Here is how to turn all of that off.

## Disable GitHub Copilot

Open **Settings** (`Cmd+,` / `Ctrl+,`), search for `copilot`, and set:

```json
"github.copilot.enable": {
  "*": false
}
```

This disables Copilot suggestions across all file types. You can also disable it for Lean only by replacing `"*"` with `"lean4"`.

## Disable formatting and autocomplete for Lean

Add a language-specific block for Lean 4:

```json
"[lean4]": {
  "editor.formatOnSave": false,
  "editor.formatOnType": false,
  "editor.acceptSuggestionOnEnter": "off",
  "editor.snippetSuggestions": "none",
  "editor.wordBasedSuggestions": "off"
}
```

- **`formatOnSave` / `formatOnType`** — prevents the formatter from rewriting whitespace in your proofs
- **`acceptSuggestionOnEnter`** — stops `Enter` from inserting a suggestion when you just want a newline
- **`snippetSuggestions` / `wordBasedSuggestions`** — removes noise from the autocomplete menu, leaving only Lean's own completions

## Where to put these settings

Open the command palette (`Cmd+Shift+P` / `Ctrl+Shift+P`) and run **Preferences: Open User Settings (JSON)**. Add the blocks above at the top level of the JSON object.
