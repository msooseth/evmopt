# Run gasol_asm.py with its temp dir under $GASOL_TMP (gasol hard-codes /tmp/). Usage: gasol_tmp.py <gasol args>
import os, runpy, sys
gasol = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "gasol-optimizer")
sys.path.insert(0, gasol)
import global_params.paths as P
P.tmp_path = os.environ["GASOL_TMP"].rstrip("/") + "/"
P.gasol_path = P.tmp_path + P.gasol_folder + "/"
P.json_path = P.gasol_path + "jsons"
P.smt_encoding_path = P.gasol_path + "smt_encoding/"
P.solutions_path = P.gasol_path + "solutions/"
P.dot_path = P.gasol_path + "dot/"
P.csv_file = P.gasol_path + "solutions/statistics.csv"
sys.argv = [os.path.join(gasol, "gasol_asm.py")] + sys.argv[1:]
runpy.run_path(sys.argv[0], run_name="__main__")
