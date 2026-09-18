"""Exercise the built Disk Guard with isolated state and injected free space.

Usage: python3 scripts/test-disk-guard.py /nix/store/.../bin/disk-guard
The executable must use the default 60/40/20 GiB thresholds and 5 GiB margin.
"""

import os
from pathlib import Path
import subprocess
import sys
import tempfile


def main():
    binary = str(Path(sys.argv[1]).resolve(strict=True))
    with tempfile.TemporaryDirectory(prefix="disk-guard-test-") as temporary:
        root = Path(temporary)
        env = dict(os.environ, DISK_GUARD_STATE_DIR=str(root / "state"),
                   DISK_GUARD_LOG_FILE=str(root / "guard.log"),
                   DISK_GUARD_NOTIFY="/usr/bin/true",
                   DISK_GUARD_REMOTE_NOTIFY="/usr/bin/true",
                   DISK_GUARD_HEARTBEAT_FILE="")
        now = 1800000000

        def run(gib, category, remote="/usr/bin/true", rc=0, pending="none"):
            nonlocal now
            now += 300
            result = subprocess.run([binary], env=dict(
                env, DISK_GUARD_FREE_KB=str(gib * 1024 * 1024),
                DISK_GUARD_NOW=str(now), DISK_GUARD_REMOTE_NOTIFY=remote),
                capture_output=True, text=True, timeout=45)
            assert result.returncode == rc, result.stderr
            state = (root / "state/state").read_text().splitlines()
            assert state[0] == category, (gib, state)
            assert state[2] == pending, state

        for gib, category in [(61, "healthy"), (59, "warn"), (60, "warn"),
                              (64, "warn"), (65, "healthy"), (19, "urgent"),
                              (21, "urgent"), (24, "urgent"), (25, "warn"),
                              (40, "warn"), (65, "healthy")]:
            run(gib, category)
        run(19, "urgent", remote="/usr/bin/false", rc=1, pending="urgent")
        run(19, "urgent")
        assert "cleanup: skipped because test free space is injected" in (root / "guard.log").read_text()
        assert not (root / "state/last-cleanup").exists()
        result = subprocess.run([binary], env=dict(env, DISK_GUARD_FREE_KB="invalid"),
                                capture_output=True, text=True, timeout=45)
        assert result.returncode != 0
    print("PASS: thresholds, recovery margin, remote retry, invalid input, no real cleanup")


if __name__ == "__main__":
    main()
