#!/bin/sh
# --------------------------------------
# Multi-Executable-Script-Wrap (AUTO)
# --------------------------------------
help_msg()
{
    echo "usage: $1 <command> <args>" >&2
    echo "available commands:" >&2
    {% for ename in data %}
    echo "\t* {{ ename }}" >&2
    {% endfor %}
}
# --------------------------------------
error_handle()
{
    echo "<E> > $1" >&2
    help_msg
    exit 1
}
# --------------------------------------
echo "--- loading multi-executable shell wrapper ---"
# --------------------------------------
if [ "$#" -lt 2 ]
then
    error_handle "No executable selected"
fi
# --------------------------------------
if [ $1 = "help" ] || [ $1 = "-h" ] || [ $1 = "--help" ]
then
    help_msg "$0"
    exit 0
fi
# --------------------------------------
if {% for edata in data %} {{ '! [ $1 = "{}" ]'.format(edata) }} && {% endfor %} true
then
    error_handle "Unknown executable selected: $1"
fi
# --------------------------------------
if [ ! -z "$(which $1)" ]
then
    echo "--- starting $(which $1) ---"
    exec $@
fi
# --------------------------------------
if [ -x "$(dirname $0)/$1" ]
then
    echo "--- starting $(dirname $0)/$1 ---"
    exec "$(dirname $0)/$1" ${@:2}
fi
# --------------------------------------
error_handle "Could not find actual executable for $1"
# --------------------------------------
