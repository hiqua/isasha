# Explore the theories given.
# ISABELLE_BIN_PATH must contain the path to the Isabelle binary.
isplore(){
  for f in $@; do
    theory_name=`basename -s ".thy" "$f"`
    new_theory_name=$theory_name"_""`date +%s`"
    new_filename=$new_theory_name".thy"
    cp "$f" /tmp/$new_filename
    sed -i'' "s/ $theory_name$/ $new_theory_name/" /tmp/$new_filename
    chmod u-w /tmp/$new_filename
    /.$ISABELLE_BIN_PATH /tmp/$new_filename
  done;
}
