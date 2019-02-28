#!/bin/bash

set -Eeuo pipefail

if (( ${BASH_VERSION%%.*} < 4 )); then echo "ERROR: [bash] version 4.0+ required!" ; exit -1 ; fi

ROOT="$(cd -P -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)/.."

LOGS_DIR=""

BENCHMARKS_DIR=""
STATS_EXT=".stats"
SYGUS_EXT=".sl"

usage() {
  if [ -n "$1" ]; then echo -e "\nERROR: $1" >&2 ; fi
  echo -en "
Usage: $0 [options] <logs_path>

Configuration:
    --benchmarks, -b <path>
" 1>&2 ; exit -1
}

for opt in "$@"; do
  shift
  case "$opt" in
    "--benchmark")    set -- "$@" "-b" ;;

    "--")             set -- "$@" "--" ;;
    "--"*)            usage "Unrecognized option: $opt." ;;
    *)                set -- "$@" "$opt"
  esac
done

while getopts ':b:' OPTION ; do
  case "$OPTION" in
    "b" ) [ -d "$OPTARG" ] || usage "Target directory [$OPTARG] not found."
          BENCHMARKS_DIR="`realpath "$OPTARG"`" ;;
      * ) usage "Unrecognized option: -$OPTARG." ;;
  esac
done
shift $(($OPTIND -1))

[ -d "$BENCHMARKS_DIR" ] || usage "Benchmarks directory [$BENCHMARKS_DIR] not found."

LOGS_DIR="$1"
RESULTS_FILE="$LOGS_DIR/results.csv"

[ -d "$LOGS_DIR" ] || usage "Logs directory [$TESTCASE] not found."
[ -f "$RESULTS_FILE" ] || usage "`results.csv` not found in logs directory."

cat "$RESULTS_FILE" | head -n 1 | tr '\n' ','
echo 'CounterExamples'

for TESTCASE in `find "$BENCHMARKS_DIR" -name *$SYGUS_EXT` ; do
  TESTCASE_NAME=${TESTCASE#$BENCHMARKS_DIR/}
  TESTCASE_NAME=${TESTCASE_NAME%$SYGUS_EXT}
  TESTCASE_PREFIX="$LOGS_DIR/$TESTCASE_NAME"

  grep "$TESTCASE" "$RESULTS_FILE" | tr '\n' ','
  if [ -f "$TESTCASE_PREFIX.stats" ]; then
    grep -oP 'lig_ce \K[0-9.]+' "$TESTCASE_PREFIX.stats"
  else
    echo "-"
  fi
done
