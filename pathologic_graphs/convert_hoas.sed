s/--.*//
s/sort([[:digit:]]*)/"sort\1"/g
s/^"sort/; "sort/
s/cmix([[:digit:]]*)/; "cmix\1"/
s/clam([[:digit:]]*)/; "clam\1"/
s/:/:=/
s/\(/{{/
s/\)/}}/
s/Type/Sort/
