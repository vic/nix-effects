# nix-effects benchmarks: test suite, applications, stress tests, and runner tools.
#
# Pure expressions (tests, apps, stress) work with just lib.
# Runner derivations (run, compare) require pkgs - only exposed when passed.
#
# Usage:
#   nix eval --file ./bench tests                    # test suite
#   nix eval --file ./bench apps.interp.fib15        # interpreter
#   nix build -f . nix.nix-effects.bench.run         # runner script (needs pkgs)
#   ./result/bin/nix-effects-bench --name v0.1.0     # run benchmarks
{ lib ? (import <nixpkgs> {}).lib, pkgs ? null }:

let
  fx = import ../. { inherit lib pkgs; };
  interp = import ../apps/interp { inherit fx; };
  buildSim = import ../apps/build-sim { inherit fx; };
  stress = import ./stress { inherit fx; };

  # Pure benchmark expressions (no derivations needed)
  expressions = {
    tests = fx.tests.allPass;

    apps = {
      interp = {
        fib10 = interp.run interp.exprs.benchmarks.fib10;
        fib15 = interp.run interp.exprs.benchmarks.fib15;
        fib20 = interp.run interp.exprs.benchmarks.fib20;
        fib25 = interp.run interp.exprs.benchmarks.fib25;

        lets100 = interp.run interp.exprs.benchmarks.lets100;
        lets500 = interp.run interp.exprs.benchmarks.lets500;
        lets1000 = interp.run interp.exprs.benchmarks.lets1000;

        sum100 = interp.run interp.exprs.benchmarks.sum100;
        sum1000 = interp.run interp.exprs.benchmarks.sum1000;
        sum5000 = interp.run interp.exprs.benchmarks.sum5000;

        countdown1000 = interp.run interp.exprs.benchmarks.countdown1000;
        countdown10000 = interp.run interp.exprs.benchmarks.countdown10000;

        ack32 = interp.run interp.exprs.benchmarks.ack32;
        ack33 = interp.run interp.exprs.benchmarks.ack33;
      };

      buildSim = {
        linear50 = (buildSim.evalQuiet buildSim.graphs.benchmarks.linear50).value;
        linear100 = (buildSim.evalQuiet buildSim.graphs.benchmarks.linear100).value;
        linear200 = (buildSim.evalQuiet buildSim.graphs.benchmarks.linear200).value;
        linear500 = (buildSim.evalQuiet buildSim.graphs.benchmarks.linear500).value;

        wide50 = (buildSim.evalQuiet buildSim.graphs.benchmarks.wide50).value;
        wide100 = (buildSim.evalQuiet buildSim.graphs.benchmarks.wide100).value;
        wide200 = (buildSim.evalQuiet buildSim.graphs.benchmarks.wide200).value;
        wide500 = (buildSim.evalQuiet buildSim.graphs.benchmarks.wide500).value;

        diamond5 = (buildSim.evalQuiet buildSim.graphs.benchmarks.diamond5).value;
        diamond8 = (buildSim.evalQuiet buildSim.graphs.benchmarks.diamond8).value;
        diamond10 = (buildSim.evalQuiet buildSim.graphs.benchmarks.diamond10).value;

        tree5 = (buildSim.evalQuiet buildSim.graphs.benchmarks.tree5).value;
        tree8 = (buildSim.evalQuiet buildSim.graphs.benchmarks.tree8).value;

        mixed_small = (buildSim.evalQuiet buildSim.graphs.benchmarks.mixed_small).value;
        mixed_medium = (buildSim.evalQuiet buildSim.graphs.benchmarks.mixed_medium).value;
        mixed_large = (buildSim.evalQuiet buildSim.graphs.benchmarks.mixed_large).value;

        fail_early = (buildSim.evalQuiet buildSim.graphs.benchmarks.linear_fail_early).error or "no error";
        fail_mid = (buildSim.evalQuiet buildSim.graphs.benchmarks.linear_fail_mid).error or "no error";
        fail_late = (buildSim.evalQuiet buildSim.graphs.benchmarks.linear_fail_late).error or "no error";
      };
    };

    stress = {
      effectHeavy = stress.bench.effectHeavy;
      bindHeavy = stress.bench.bindHeavy;
      mixed = stress.bench.mixed;
      rawGC = stress.bench.rawGC;
      deepChains = stress.bench.deepChains;
      nestedHandlers = stress.bench.nestedHandlers;
    };
  };

  # Derivations - only when pkgs is provided
  derivations = if pkgs == null then {} else {
    # Benchmark runner derivation
    run = pkgs.writeShellApplication {
      name = "nix-effects-bench";
      runtimeInputs = with pkgs; [ nix coreutils ];
      meta.description = "Run nix-effects benchmarks with named history";
      text = ''
        # Benchmark runner with named history.
        # Usage:
        #   nix-effects-bench                      # output to stdout only
        #   nix-effects-bench --quick              # single run (faster)
        #   nix-effects-bench --name v0.1.0        # save as version
        #   nix-effects-bench --name pre-fused     # save as milestone

        # Ensure consistent numeric formatting (decimal point, not comma)
        export LC_NUMERIC=C

        BENCH_DIR="''${BENCH_DIR:-bench}"
        if [[ ! -d "$BENCH_DIR" ]]; then
          echo "Error: bench directory not found: $BENCH_DIR" >&2
          echo "Run from nix-effects root or set BENCH_DIR=/path/to/bench" >&2
          exit 1
        fi
        BENCH_DIR=$(realpath "$BENCH_DIR")

        NAME=""
        RUNS=3
        while [[ $# -gt 0 ]]; do
            case "$1" in
                --name) NAME="$2"; shift 2 ;;
                --quick) RUNS=1; shift ;;
                *) echo "Unknown arg: $1" >&2; exit 1 ;;
            esac
        done

        declare -A results

        TOTAL=0
        DONE=0

        count_benchmarks() {
            TOTAL=$((1 + 8 + 12 + 8))
        }
        count_benchmarks

        run_bench() {
            local target="$1"
            DONE=$((DONE + 1))
            echo "[$DONE/$TOTAL] $target ..." >&2
            local times=()
            for i in $(seq 1 "$RUNS"); do
                local start end ms rc
                start=$(date +%s%N)
                rc=0
                nix eval --impure --expr "(import $BENCH_DIR {}).$target" >/dev/null 2>&1 || rc=$?
                end=$(date +%s%N)
                if (( rc != 0 )); then
                    echo "  FAILED (exit $rc, skipping)" >&2
                    results["$target"]=-1
                    return
                fi
                ms=$(( (end - start) / 1000000 ))
                times+=("$ms")
                echo "  run $i: ''${ms}ms" >&2
            done
            local median
            if (( RUNS == 1 )); then
                median="''${times[0]}"
            else
                median=$(printf '%s\n' "''${times[@]}" | sort -n | head -n2 | tail -n1)
            fi
            results["$target"]=$median
        }

        echo "Running $TOTAL benchmarks ($RUNS runs each)..." >&2

        run_bench tests
        for b in fib10 fib15 fib20 lets100 lets500 sum100 sum1000 countdown1000; do
            run_bench "apps.interp.$b"
        done
        for b in linear50 linear100 linear200 wide50 wide100 wide200 diamond5 diamond8 tree5 tree8 mixed_small mixed_medium; do
            run_bench "apps.buildSim.$b"
        done
        for b in effectHeavy bindHeavy mixed rawGC; do
            run_bench "stress.$b.s10k"
            run_bench "stress.$b.s100k"
        done

        fmt_ms() {
            if (( $1 < 0 )); then printf "FAIL"; else printf "%s" "$1"; fi
        }

        # Generate JSON
        gen_json() {
            echo "{"
            echo "  \"name\": \"''${NAME:-unnamed}\","
            echo "  \"timestamp\": \"$(date -Iseconds)\","
            echo "  \"nix\": \"$(nix --version | cut -d' ' -f3)\","
            echo "  \"system\": \"$(uname -sm)\","
            echo "  \"results\": {"
            local first=true
            for key in $(printf '%s\n' "''${!results[@]}" | sort); do
                local v="''${results[$key]}"
                if (( v < 0 )); then continue; fi
                $first || echo ","
                first=false
                printf '    "%s": %s' "$key" "$v"
            done
            echo ""
            echo "  }"
            echo "}"
        }

        # Generate markdown
        gen_md() {
            echo "# Benchmark: ''${NAME:-unnamed}"
            echo ""
            echo "- **Timestamp**: $(date -Iseconds)"
            echo "- **Nix**: $(nix --version)"
            echo "- **System**: $(uname -srm)"
            echo ""
            echo "## Test Suite"
            printf "| %-20s | %6s |\n" "Benchmark" "ms"
            printf "|-%s-|-%s:|\n" "$(printf '%.20s' '--------------------')" "$(printf '%.6s' '------')"
            printf "| %-20s | %6s |\n" "tests" "$(fmt_ms "''${results[tests]}")"
            echo ""
            echo "## Interpreter"
            printf "| %-20s | %6s |\n" "Benchmark" "ms"
            printf "|-%s-|-%s:|\n" "$(printf '%.20s' '--------------------')" "$(printf '%.6s' '------')"
            for b in fib10 fib15 fib20 lets100 lets500 sum100 sum1000 countdown1000; do
                printf "| %-20s | %6s |\n" "$b" "$(fmt_ms "''${results[apps.interp.$b]}")"
            done
            echo ""
            echo "## Build Simulator"
            printf "| %-20s | %6s |\n" "Benchmark" "ms"
            printf "|-%s-|-%s:|\n" "$(printf '%.20s' '--------------------')" "$(printf '%.6s' '------')"
            for b in linear50 linear100 linear200 wide50 wide100 wide200 diamond5 diamond8 tree5 tree8 mixed_small mixed_medium; do
                printf "| %-20s | %6s |\n" "$b" "$(fmt_ms "''${results[apps.buildSim.$b]}")"
            done
            echo ""
            echo "## Stress Tests"
            printf "| %-20s | %6s | %6s |\n" "Benchmark" "10k" "100k"
            printf "|-%s-|-%s:|-%s:|\n" "$(printf '%.20s' '--------------------')" "$(printf '%.6s' '------')" "$(printf '%.6s' '------')"
            for b in effectHeavy bindHeavy mixed rawGC; do
                printf "| %-20s | %6s | %6s |\n" "$b" "$(fmt_ms "''${results[stress.$b.s10k]}")" "$(fmt_ms "''${results[stress.$b.s100k]}")"
            done
        }

        if [[ -n "$NAME" ]]; then
            mkdir -p "$BENCH_DIR/history"
            gen_json > "$BENCH_DIR/history/''${NAME}.json"
            gen_md > "$BENCH_DIR/history/''${NAME}.md"
            echo "Saved: $BENCH_DIR/history/''${NAME}.{json,md}" >&2
        fi

        gen_md
      '';
    };

    # Comparison tool derivation
    compare = pkgs.writeShellApplication {
      name = "nix-effects-bench-compare";
      runtimeInputs = with pkgs; [ nix ];
      meta.description = "Compare two nix-effects benchmark runs";
      text = ''
        # Compare two benchmark runs.
        # Usage: nix-effects-bench-compare <baseline> <current>
        # Example: nix-effects-bench-compare pre-fused post-fused

        BENCH_DIR="''${BENCH_DIR:-bench}"
        if [[ ! -d "$BENCH_DIR" ]]; then
          echo "Error: bench directory not found: $BENCH_DIR" >&2
          echo "Run from nix-effects root or set BENCH_DIR=/path/to/bench" >&2
          exit 1
        fi

        BENCH_DIR=$(realpath "$BENCH_DIR")

        [[ $# -eq 2 ]] || { echo "Usage: $0 <baseline> <current>" >&2; exit 1; }

        BASELINE="$1"
        CURRENT="$2"

        baseline_file="$BENCH_DIR/history/''${BASELINE}.json"
        current_file="$BENCH_DIR/history/''${CURRENT}.json"

        [[ -f "$baseline_file" ]] || { echo "Not found: $baseline_file" >&2; exit 1; }
        [[ -f "$current_file" ]] || { echo "Not found: $current_file" >&2; exit 1; }

        # shellcheck disable=SC2016
        nix eval --impure --raw --expr '
        let
          baseline = builtins.fromJSON (builtins.readFile "'"$baseline_file"'");
          current = builtins.fromJSON (builtins.readFile "'"$current_file"'");

          compare = name:
            let
              b = baseline.results.''${name} or null;
              c = current.results.''${name} or null;
            in
              if b == null || c == null then null
              else { inherit name; inherit b c; d = c - b; p = if b == 0 then 0 else ((c - b) * 100) / b; };

          keys = builtins.attrNames current.results;
          rows = builtins.filter (x: x != null) (map compare keys);

          pad = n: s: let len = builtins.stringLength s; in if len >= n then s else s + builtins.substring 0 (n - len) "                              ";
          padr = n: s: let len = builtins.stringLength s; in if len >= n then s else builtins.substring 0 (n - len) "                              " + s;

          fmtDelta = d: if d > 0 then "+''${toString d}" else toString d;
          fmtPct = p: if p > 0 then "+''${toString p}%" else "''${toString p}%";

          fmtRow = r: "| ''${pad 24 r.name} | ''${padr 6 (toString r.b)} | ''${padr 6 (toString r.c)} | ''${padr 7 (fmtDelta r.d)} | ''${padr 6 (fmtPct r.p)} |";

          header = "| ''${pad 24 "Benchmark"} | ''${padr 6 "Base"} | ''${padr 6 "Curr"} | ''${padr 7 "Delta"} | ''${padr 6 "%"} |";
          sep = "|''${builtins.substring 0 26 "--------------------------"}|''${builtins.substring 0 8 "--------"}:|''${builtins.substring 0 8 "--------"}:|''${builtins.substring 0 9 "---------"}:|''${builtins.substring 0 8 "--------"}:|";

        in "# Comparison: ''${baseline.name} → ''${current.name}\n\n" + header + "\n" + sep + "\n" + builtins.concatStringsSep "\n" (map fmtRow rows) + "\n\nNegative = faster\n"
        '
      '';
    };
  };

in expressions // derivations
