"""Verify the official preprint 1.0."""
import runpy
from pathlib import Path

runpy.run_path(str(Path(__file__).with_name("verify_preprint.py")), run_name="__main__")
