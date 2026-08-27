#!/opt/icho-answer-blind-runtime-10b04c62-tgasimple1/bin/sh
set -eu

case "$0" in
  /*) ;;
  *)
    echo "answer-blind overlay Archon entry must use an absolute path" >&2
    exit 2
    ;;
esac

overlay_scripts=${0%/*}
overlay_root=${overlay_scripts%/*}
if [ ! -d "$overlay_root/src/archon" ]; then
  echo "answer-blind overlay Archon source is missing" >&2
  exit 2
fi

unset PYTHONHOME
export PYTHONPATH="$overlay_root/src"
export PYTHONSAFEPATH=1
export PYTHONDONTWRITEBYTECODE=1
exec /opt/icho-answer-blind-runtime-10b04c62-tgasimple1/venv/bin/python -P -m archon.cli "$@"
