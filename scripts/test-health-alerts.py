"""Run isolated notification checks against a built Darwin system path."""

import os
import plistlib
import re
import subprocess
import sys
import tempfile
from pathlib import Path


def main():
    system = Path(sys.argv[1])
    with tempfile.TemporaryDirectory(prefix="health-alert-test-") as temporary:
        root = Path(temporary)
        remote = root / "remote"
        remote.write_text('#!/bin/sh\ncat >> "$ALERT_LOG"\n')
        remote.chmod(0o700)
        snapshot = root / "snapshot"
        snapshot.write_text('#!/bin/sh\necho "2027-01-15 08:00:00 UTC"\n')
        snapshot.chmod(0o700)
        success = root / "success.plist"
        success.write_bytes(plistlib.dumps({"BackupSuccessTime": "2027-01-15 08:00:00 UTC"}))
        for job, prefix in [("tm-freshness", "TM_CHECK"), ("offsite-freshness", "OFFSITE_CHECK")]:
            spec = plistlib.loads((system / f"user/Library/LaunchAgents/org.nixos.{job}.plist").read_bytes())
            command = spec["ProgramArguments"][-1]
            binary = re.search(r"exec (\S+)", command)[1]
            log = root / f"{job}.alerts"
            env = dict(os.environ, ALERT_LOG=str(log))
            env.update({f"{prefix}_{key}": value for key, value in {
                "STATE_DIR": str(root / job), "LOG_FILE": str(root / f"{job}.log"),
                "REMOTE_NOTIFY": str(remote), "HEARTBEAT_FILE": "",
                "MAX_AGE_SEC": "99999999",
            }.items()})
            env.update(TM_CHECK_REACHABLE="true", TM_CHECK_LATEST_SNAPSHOT_COMMAND=str(snapshot),
                       OFFSITE_CHECK_PLIST=str(success), OFFSITE_CHECK_COVERAGE="/usr/bin/true")

            def run(offset, broken=False):
                current = dict(env, **{f"{prefix}_NOW": str(1800000000 + offset)})
                if broken:
                    current.update(TM_CHECK_LATEST_SNAPSHOT_COMMAND="/usr/bin/false",
                                   OFFSITE_CHECK_COVERAGE="/usr/bin/false")
                result = subprocess.run([binary], env=current, capture_output=True, text=True, timeout=30)
                assert result.returncode == (1 if broken and prefix == "TM_CHECK" else 0), result.stderr
                return len(log.read_text().splitlines()) if log.exists() else 0

            assert run(0) == 0
            assert run(3600, True) == 0
            assert run(7200) == 0  # A transient failure and recovery are silent.
            assert run(10800, True) == 0
            assert run(14400, True) == 1
            assert run(18000, True) == 1
            assert run(14400 + 604799, True) == 1
            assert run(14400 + 604800, True) == 2
            assert run(14400 + 608400) == 2
    print("PASS: transient suppression, sustained alerts, weekly reminders, silent recovery")


if __name__ == "__main__":
    main()
