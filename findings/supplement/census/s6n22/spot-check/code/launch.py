#!/usr/bin/env python3
"""launch.py (wave8/s6spot): start code/driver.sh detached (new session, nice 10), print its PID.
Environment passed through: W, STOP_EPOCH, KILL_EPOCH."""
import os, subprocess, pathlib
D = pathlib.Path(__file__).resolve().parent.parent
log = open(D / "logs" / "driver.out", "a")
p = subprocess.Popen(["nice", "-n", "10", str(D / "code" / "driver.sh")], cwd=D, stdin=subprocess.DEVNULL,
                     stdout=log, stderr=subprocess.STDOUT, start_new_session=True)
(D / "logs" / "driver.pid").write_text(f"{p.pid}\n")
print(p.pid)
