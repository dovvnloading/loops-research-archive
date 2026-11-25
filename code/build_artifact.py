#!/usr/bin/env python3
"""Compatibility entry point for the replacement LOOPS web application build.

The old self-contained dossier has been retired. Research inputs are preserved;
Vite and the archive packaging step now produce the deployable dist/ directory.
"""
from pathlib import Path
import subprocess

if __name__ == "__main__":
    subprocess.run(["npm", "run", "build"], cwd=Path(__file__).resolve().parents[1], check=True)
