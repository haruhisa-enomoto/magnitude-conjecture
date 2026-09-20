"""Check command boundaries and restriction preservation without running Lean."""

import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest


WRAPPER = Path(__file__).resolve().parents[1] / "scripts/landrun-wrapper.sh"


class LandrunWrapperTest(unittest.TestCase):
    def invoke(self, args):
        with tempfile.TemporaryDirectory() as directory:
            stub = Path(directory) / "capture"
            stub.write_text("#!/usr/bin/env python3\nimport json,sys\nprint(json.dumps(sys.argv[1:]))\n")
            stub.chmod(0o755)
            return subprocess.run(
                [str(WRAPPER), *args],
                env={**os.environ, "PALOMAR_LANDRUN_BIN": str(stub)},
                capture_output=True, text=True,
            )

    def test_current_and_legacy_command_boundaries(self):
        for separator in ([], ["--"]):
            with self.subTest(separator=separator):
                result = self.invoke(["--ro", "/path with spaces", *separator,
                                      "lean4export", "Challenge", "--", "target"])
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(json.loads(result.stdout), ["--ro", "/path with spaces",
                                 "--", "lean4export", "Challenge", "--", "target"])

    def test_restriction_disabling_flags_are_rejected(self):
        for flag in ("-unrestricted-filesystem", "--unrestricted-network"):
            result = self.invoke([flag, "--", "lean4export"])
            self.assertEqual(result.returncode, 2)
            self.assertEqual(result.stdout, "")
            self.assertIn("switches off part of the sandbox", result.stderr)

    def test_missing_command_is_rejected(self):
        result = self.invoke(["--ro", "/tmp", "--"])
        self.assertEqual(result.returncode, 2)
        self.assertIn("no sandboxed command", result.stderr)

    def test_unknown_option_is_rejected(self):
        result = self.invoke(["--unknown", "lean4export"])
        self.assertEqual(result.returncode, 2)
        self.assertEqual(result.stdout, "")


if __name__ == "__main__":
    unittest.main()
