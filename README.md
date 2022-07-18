
# Transfinite Meta-Programming

A proof-of-concept implementation of a transfinite meta-programming language with ordinal De Bruijn indices.

See some example traces in [](./src/traces/tfdbi/).

For more info, see:
- https://medium.com/@thealexvarga/transfinite-meta-posting-c57f10d40975
- https://medium.com/@thealexvarga/transfinite-meta-programming-a068a38cbdca

# TODO

- Try to unify `quo` with `qq` into a single type case to reduce redundant processing of subterms of `qq`s
- Provide more automatic handling of index shifting, as in TaPL 6.2
- Simplify the `mk_*` functions and their usage (and likely remove bugs)

# Use

## Run

- To run once: `sbt run`
- To run on file changes: `sbt "~ run"`
  - or just `./run`
  - I recommend `./run > local/out.tfdbi` with VS Code's Log Viewer extension

## Syntax

- symlink to `src/tfdbi-syntax` from vscode extensions folder
- add this to `.vscode/settings.json`:

```json
{
  "...": "...",
  "logViewer.watch": [
    {
      "title": "Out",
      "pattern": "<path_to_project>/local/out.tfdbi"
    }
  ]
}
```

## Test

- `sbt test` or `./test`
- test a single file like `sbt "test:testOnly *TestEval"`

