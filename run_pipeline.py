# -*- coding: utf-8 -*-
"""Полный запуск демонстрационного pipeline Kodolov.
Запуск:
    python run_pipeline.py plan.pdf
или:
    python run_pipeline.py plan.pdf --page 3 --print-scale 50
"""
import argparse
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve()
PARSER = HERE.with_name("plan_to_3d_p2_5.py")
FURNITURE = HERE.with_name("add_furniture_p2_6.py")
EXPORT = HERE.with_name("export_excel_p2_6.py")

ap = argparse.ArgumentParser()
ap.add_argument("pdf")
ap.add_argument("--page", type=int, default=-1, help="номер листа с нуля; -1 = авто")
ap.add_argument("--print-scale", type=float, default=50)
ap.add_argument("--out", default="model.glb")
args = ap.parse_args()

pdf = Path(args.pdf).resolve()
glb = Path(args.out).resolve()
json_path = glb.with_suffix(".json")
furnished = glb.with_name(glb.stem + "_furnished.glb")
excel = glb.with_name(glb.stem + "_estimate.xlsx")

cmd1 = [sys.executable, str(PARSER), str(pdf), "--out", str(glb),
        "--print-scale", str(args.print_scale), "--debug", "--door-debug"]
if args.page >= 0:
    cmd1 += ["--page", str(args.page)]

print("\n=== 1/3 PDF → 3D + JSON ===")
subprocess.run(cmd1, check=True)

print("\n=== 2/3 JSON + GLB → мебель ===")
subprocess.run([sys.executable, str(FURNITURE), str(json_path), str(furnished), str(glb)], check=True)

print("\n=== 3/3 JSON → Excel ===")
subprocess.run([sys.executable, str(EXPORT), str(furnished.with_suffix(".json")), str(excel)], check=True)

print("\nГОТОВО")
print("3D:", furnished)
print("JSON:", furnished.with_suffix(".json"))
print("Excel:", excel)
