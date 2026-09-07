# API documentation

This separate project pins doc-gen4 to its Lean 4.33.1 release. Documentation
dependencies do not enter the proof package's dependency list.

After building the root package, run:

```sh
python3 ../scripts/build_lean_serial.py --package . --output ../.build-audit/doc-tool \
  --max-rss-kib 8388608 doc-gen4
cd ..
python3 scripts/build_api.py
python3 scripts/build_website.py
python3 scripts/check_website.py
```

The committed manifest pins this separate project's dependencies. The generator
documents every production library module serially, using doc-gen4's SQLite database and
HTML/search renderer. It links dependency imports to their exact source
revisions, without regenerating Mathlib's entire documentation site.

Generated API pages are copied into `_site/api/`. The API records its own
source commit in `.lake/build/api-build.json`; the website also records the
revision of its handwritten pages. After Lean sources change, remove the
ignored documentation build directory and regenerate to obtain a new revision.
Only one API generation process may write its database at a time.
