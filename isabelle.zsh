# Explore the theories given.
# "isabelle" is an alias to ./bin/isabelle
isplore(){
  for f in $@; do
  if [ -r $f ]; then
    theory_name=`basename -s ".thy" "$f"`
    new_theory_name=$theory_name"_""`date +%s`"
    new_filename=$new_theory_name".thy"
    cp "$f" /tmp/$new_filename
    sed -i'' "s/ $theory_name$/ $new_theory_name/" /tmp/$new_filename
    #chmod u-w /tmp/$new_filename
    isabelle /tmp/$new_filename &
    else
    echo "File "$f" unreadable"
  fi
  done;
}
