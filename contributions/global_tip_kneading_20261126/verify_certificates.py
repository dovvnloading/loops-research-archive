#!/usr/bin/env python3
"""Reproduce the exact checked parameter-cover data without changing it."""
from pathlib import Path
import runpy

runpy.run_path(str(Path(__file__).with_name("generate_certificates.py")), run_name="__main__")
