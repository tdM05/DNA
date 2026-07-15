#!/usr/bin/env bash
#SBATCH --job-name=euclid_timing
#SBATCH --partition=cpunodes
#SBATCH --constraint=EPYC_9634
#SBATCH --exclusive
#SBATCH --nodes=1
#SBATCH --time=3-00:00:00
#SBATCH --output=/h/56/taddmao/code/autoform/DNA/reproducable_experiments/compile_time/slurm_output/%x_%j.out
#SBATCH --error=/h/56/taddmao/code/autoform/DNA/reproducable_experiments/compile_time/slurm_err/%x_%j.err
set -uo pipefail
# SLURM copies this script to /var/spool/slurmd/...; BASH_SOURCE would point there, so hardcode.
HERE="/h/56/taddmao/code/autoform/DNA/reproducable_experiments/compile_time"
export PATH="/u/taddmao/.venvs/leaneuclid/bin:$PATH"   # z3, cvc5
export CAP="${CAP:-3600}" NUM_RUNS="${NUM_RUNS:-5}"
mkdir -p "$HERE/results"
{ echo "host: $(hostname)"; echo "date: $(date)"; echo "cap:  ${CAP}s  num_runs: ${NUM_RUNS}";
  echo "git:  $(git -C "$HERE" rev-parse HEAD)"; echo "z3:   $(which z3)  cvc5: $(which cvc5)";
  echo; lscpu | grep -E 'Model name|Socket|Core|Thread'; } > "$HERE/results/run_meta_${SLURM_JOB_ID:-local}.txt"
bash "$HERE/run_timing.sh"
