#!/bin/bash

set -Euo pipefail

if (( ${BASH_VERSION%%.*} < 4 )); then echo "ERROR: [bash] version >= 4.0 required!" ; exit -1 ; fi

EXIT_CODE_BUILD_ERROR=-3
EXIT_CODE_USAGE_ERROR=-2

EXIT_CODE_PROCESS_ERROR=1
EXIT_CODE_RECORD_ERROR=2
EXIT_CODE_INFER_ERROR=3
EXIT_CODE_TIMEOUT=4

SELF_DIR="$(cd -P -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)"

BIN_DIR="$SELF_DIR/_build/install/default/bin"

PROCESS="$BIN_DIR/lig-process"
RECORD="$BIN_DIR/lig-record"
INFER="$BIN_DIR/lig-infer"
VERIFY="$BIN_DIR/lig-verify"

if [ ! -f $PROCESS ] || [ ! -f $RECORD ] || [ ! -f $INFER ] || [ ! -f $VERIFY ]; then
  echo -en "
One or more dependencies not found. Building OCaml modules ...
" >&2 ; dune build || exit $EXIT_CODE_BUILD_ERROR
fi

trap 'jobs -p | xargs kill -TERM > /dev/null 2> /dev/null' INT
trap "kill -KILL -`ps -o ppid= $$` > /dev/null 2> /dev/null" QUIT TERM

INTERMEDIATES_DIR="$SELF_DIR/_log"
SYGUS_EXT=".sl"
Z3_PATH="$SELF_DIR/_dep/z3"

INFER_TIMEOUT=86400
MIN_INFER_TIMEOUT=5

RECORD_TIMEOUT=0.5s
RECORD_FORKS=4
RECORD_STATES_PER_FORK=256
MIN_RECORD_STATES_PER_FORK=63

EXPRESSIVENESS_LEVEL=4

PROCESS_ARGS=""
RECORD_ARGS=""
INFER_ARGS=""
VERIFY_ARGS=""

declare -A DO_LOG
DO_LOG[process]="no"
DO_LOG[record]="no"
DO_LOG[infer]="no"
DO_LOG[verify]="no"

STATS_ARG=""
DO_CLEAN="no"
DO_VERIFY="no"

show_status() {
  printf "%s%16s" "$1" >&2
  printf %0"$(( ${#1} + 16 ))"d | tr 0 \\b >&2
}

usage() {
  if [ -n "$1" ]; then echo -e "\nERROR: $1" >&2 ; fi
  echo -en "
Usage: $0 [options] <benchmark.sl>

Flags:
    [--clean-intermediates, -c]
    [--verify, -v]

Configuration:
    [--expressiveness-level, -L <int>]  (4)\t    {1 = Eq .. 4 = Polyhedra .. 6 = Peano}
    [--infer-timeout, -t <seconds>]     ($INFER_TIMEOUT)\t    {> $MIN_INFER_TIMEOUT}
    [--intermediates-dir, -p <path>]    (_log)
    [--log, -l <src_1>[,<src_2>...]]    ()\t    src <- {process|record|infer|verify}
    [--states-to-record, -s <count>]    ($RECORD_STATES_PER_FORK)\t    {> $MIN_RECORD_STATES_PER_FORK}
    [--stats-path, -S <path>]           ()
    [--z3-path, -z <path>]              (_dep/z3)

Arguments to Internal Programs (@ `dirname $RECORD`):
    [--Process-args, -P \"<args>\"]   see \``basename "$PROCESS"` -h\` for details
    [--Record-args, -R \"<args>\"]    see \``basename "$RECORD"` -h\` for details
    [--Infer-args, -I \"<args>\"]     see \``basename "$INFER"` -h\` for details
    [--Verify-args, -V \"<args>\"]    see \``basename "$VERIFY"` -h\` for details
" >&2 ; exit $EXIT_CODE_USAGE_ERROR
}

for opt in "$@"; do
  shift
  case "$opt" in
    "--Process-args")         set -- "$@" "-P" ;;
    "--Record-args")          set -- "$@" "-R" ;;
    "--Infer-args")           set -- "$@" "-I" ;;
    "--Verify-args")          set -- "$@" "-V" ;;

    "--clean-intermediates")  set -- "$@" "-c" ;;
    "--verify")               set -- "$@" "-v" ;;

    "--log")                  set -- "$@" "-l" ;;
    "--expressiveness-level") set -- "$@" "-L" ;;
    "--intermediates-path")   set -- "$@" "-p" ;;
    "--states-to-record")     set -- "$@" "-s" ;;
    "--stats-path")           set -- "$@" "-S" ;;
    "--infer-timeout")        set -- "$@" "-t" ;;
    "--z3-path")              set -- "$@" "-z" ;;

    "--")                     set -- "$@" "--" ;;
    "--"*)                    usage "Unrecognized option: $opt." ;;
    *)                        set -- "$@" "$opt"
  esac
done

OPTIND=1
while getopts ':P:R:I:V:cvl:L:p:s:S:t:z:' OPTION ; do
  case "$OPTION" in
    "P" ) PROCESS_ARGS="$OPTARG" ;;
    "R" ) RECORD_ARGS="$OPTARG" ;;
    "I" ) INFER_ARGS="$OPTARG" ;;
    "V" ) VERIFY_ARGS="$OPTARG" ;;

    "c" ) DO_CLEAN="yes" ;;
    "v" ) DO_VERIFY="yes" ;;

    "l" ) for LOG_SRC in `echo "$OPTARG" | tr ',' '\n' | sort -u | tr '\n' ' '` ; do
            case "$LOG_SRC" in
              process | record | infer | verify ) DO_LOG[$LOG_SRC]="yes" ;;
              * ) usage "Unknown source [$LOG_SRC] for logging."
            esac
          done
          ;;
    "L" ) [ "$OPTARG" -ge "1" ] && [ "$OPTARG" -le "6" ] \
            || usage "The expressiveness level (= $OPTARG) must be between 1 and 6 (both inclusive)."
          EXPRESSIVENESS_LEVEL="$OPTARG"
          ;;
    "p" ) INTERMEDIATES_DIR="$OPTARG"
          ;;
    "s" ) [ "$OPTARG" -gt "$MIN_RECORD_STATES_PER_FORK" ] \
            || usage "The number of states to record (= $OPTARG) must be > $MIN_RECORD_STATES_PER_FORK."
          STATES="$OPTARG"
          ;;
    "S" ) rm -rf $OPTARG
          STATS_ARG="-t $OPTARG"
          ;;
    "t" ) [ "$OPTARG" -gt "$MIN_INFER_TIMEOUT" ] \
            || usage "The inference timeout (= $OPTARG) must be > $MIN_INFER_TIMEOUT."
          INFER_TIMEOUT="$OPTARG"
          ;;
    "z" ) [ -f "$OPTARG" ] || usage "Z3 [$OPTARG] not found."
          Z3_PATH="$OPTARG"
          ;;
      * ) usage "Unrecognized option: -$OPTARG." ;;
  esac
done
shift $(($OPTIND -1))

[ -d "$INTERMEDIATES_DIR" ] || mkdir -p "$INTERMEDIATES_DIR"
[ -d "$INTERMEDIATES_DIR" ] \
  || usage "Intermediates directory [$INTERMEDIATES_DIR] not found."

TESTCASE="$1"
[ -f "$TESTCASE" ] || usage "Input file [$TESTCASE] not found."

TESTCASE_NAME="`basename "$TESTCASE" "$SYGUS_EXT"`"
TESTCASE_PREFIX="$INTERMEDIATES_DIR/$TESTCASE_NAME"

TESTCASE_PROCESSED="$TESTCASE_PREFIX.pro"
TESTCASE_INVARIANT="$TESTCASE_PREFIX.inv"

TESTCASE_ALL_LOG="$TESTCASE_PREFIX.log"
TESTCASE_REC_LOG="$TESTCASE_PREFIX.rlog"

TESTCASE_REC_STATES="$TESTCASE_PREFIX.rstates"
TESTCASE_ALL_STATES="$TESTCASE_PREFIX.states"

RECORD="$RECORD -z $Z3_PATH"
INFER="$INFER -z $Z3_PATH"
VERIFY="$VERIFY -z $Z3_PATH"

INFER_TIMEOUT="${INFER_TIMEOUT}s"

[ -z "${DO_LOG[process]}" ] || DO_LOG[process]="-l $TESTCASE_ALL_LOG"
[ -z "${DO_LOG[record]}" ] || DO_LOG[record]="-l $TESTCASE_REC_LOG"
[ -z "${DO_LOG[infer]}" ] || DO_LOG[infer]="-l $TESTCASE_ALL_LOG"
[ -z "${DO_LOG[verify]}" ] || DO_LOG[verify]="-l $TESTCASE_ALL_LOG"

rm -rf "$TESTCASE_REC_STATES"? $TESTCASE_ALL_STATES &
echo -en '' > "$TESTCASE_INVARIANT" &
echo -en '' > "$TESTCASE_ALL_LOG"


show_status "(processsing)"

$PROCESS -o "$TESTCASE_PROCESSED" "$TESTCASE" ${DO_LOG[process]} $PROCESS_ARGS >&2
[ $? == 0 ] || exit $EXIT_CODE_PROCESS_ERROR


wait
show_status "(recording)"

for i in `seq 1 $RECORD_FORKS` ; do
  [ -z "${DO_LOG[record]}" ] || LOG_PARAM="${DO_LOG[record]}$i"
  (timeout $RECORD_TIMEOUT \
           $RECORD -s $RECORD_STATES_PER_FORK -e "seed$i" $LOG_PARAM $RECORD_ARGS \
                   "$TESTCASE_PROCESSED") > "$TESTCASE_REC_STATES$i" &
done
wait

grep -hv "^[[:space:]]*$" "$TESTCASE_REC_STATES"? | sort -u > "$TESTCASE_ALL_STATES"

[ -z "${DO_LOG[record]}" ] || cat "$TESTCASE_REC_LOG"? >> "$TESTCASE_ALL_LOG" 2> /dev/null || true


show_status "(inferring)"

timeout --foreground $INFER_TIMEOUT \
        $INFER -s "$TESTCASE_ALL_STATES" -e "$EXPRESSIVENESS_LEVEL" $INFER_ARGS \
               ${DO_LOG[infer]} ${STATS_ARG} "$TESTCASE_PROCESSED" > "$TESTCASE_INVARIANT"
INFER_RESULT_CODE=$?


if [ "$DO_VERIFY" = "yes" ]; then
  if [ $INFER_RESULT_CODE == 124 ] || [ $INFER_RESULT_CODE == 137 ]; then
    echo > "$TESTCASE_INVARIANT" ; echo -n "[TIMEOUT] "
  fi

  show_status "(verifying)"

  $VERIFY -s "$TESTCASE" ${DO_LOG[verify]} $VERIFY_ARGS "$TESTCASE_INVARIANT" \
    > "$TESTCASE_PREFIX.result"
  RESULT_CODE=$?

  show_status "" ; cat "$TESTCASE_PREFIX.result"
elif [ $INFER_RESULT_CODE == 0 ]; then
  cat "$TESTCASE_INVARIANT" ; echo
  RESULT_CODE=0
else
  show_status "(fail)"
  RESULT_CODE=$EXIT_CODE_INFER_ERROR
  if [ $INFER_RESULT_CODE == 124 ] || [ $INFER_RESULT_CODE == 137 ]; then
    RESULT_CODE=$EXIT_CODE_TIMEOUT
  fi
  echo ""
fi


if [ "$DO_CLEAN" == "yes" ]; then
  rm -rf "$TESTCASE_REC_STATES"? "$TESTCASE_REC_LOG"?
  if [ $RESULT_CODE == 0 ] || [ $RESULT_CODE == 2 ]; then
    rm -rf "$TESTCASE_PROCESSED" "$TESTCASE_ALL_STATES"
  fi
fi

exit $RESULT_CODE
