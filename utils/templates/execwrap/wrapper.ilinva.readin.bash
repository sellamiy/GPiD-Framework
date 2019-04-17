#!/bin/bassh
# --------------------------------------
# Ilinva Wrapper for Readin (minimal) (AUTO)
# --------------------------------------
help_msg()
{
    echo "usage: $1 <readin> <readout>" >&2
}
# --------------------------------------
error_handle()
{
    echo "<E> > $1" >&2
    help_msg
    exit 1
}
# --------------------------------------
echo "--- loading ilinva readin shell wrapper ---"
# --------------------------------------
if [ "$#" -lt 2 ]
then
    error_handle "Not enough argument"
fi
# --------------------------------------
readin=$1
readout=$2
forward=${@:3}
# --------------------------------------
related_abducible_name()
{
    inputabd="$(dirname $1)"/"$(basename -s .mlw $1)".abd
}
# --------------------------------------
related_output_name()
{
    outputfile="$2"/"$(basename -s .mlw $1)".out.mlw
}
# --------------------------------------
executable=ilinva-w3wml
# --------------------------------------
for inputfile in "$readin"/*.mlw
do
    related_abducible_name "$inputfile"
    related_output_name "$inputfile" "$readout"

    if [ ! -z "$(which $executable)" ]
    then
        echo "--- starting $(which $executable) on $inputfile ---"
        $executable -i "$inputfile" -a "$inputabd" -o "$outputfile" $forward
    # --------------------------------------
    elif [ -x "$(dirname $0)/$executable" ]
    then
        echo "--- starting $(dirname $0)/$executable on $inputfile ---"
        "$(dirname $0)/$executable" -i "$inputfile" -a "$inputabd" -o "$outputfile" $forward
    fi
done
# --------------------------------------
