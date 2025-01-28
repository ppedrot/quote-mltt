print "digraph logrel_deps {\n";
# See here for color schemes: https://graphviz.org/doc/info/colors.html
print "  node [shape = ellipse,style=filled,colorscheme = paired12];\n";
print "  subgraph cluster_autosubst { label=\"AutoSubst\" \n}";
print "  subgraph cluster_syntax { label=\"Syntax\" \n}";
print "  subgraph cluster_logrel { label=\"LogicalRelation\" \n}";
print "  subgraph cluster_subst { label=\"Validity\" \n}";
print "  subgraph cluster_typing { label=\"Typing Properties\" \n}";
print "  subgraph cluster_algo { label=\"Algorithmic\" \n}";
print "  subgraph cluster_dec { label=\"Decidability\" \n}";
while (<>) {
  if (m/.*?theories\/([^\s]*)\.vo.*:(.*)/) {
    $dests = $2 ;
    ($path,$src) = ($1 =~ s/\//\./rg =~ m/(.*\.)?([^.]*)$/);
    if ($path =~ m/AutoSubst\./) {
      print "subgraph cluster_autosubst { \"$path$src\"[label=\"$src\",fillcolor=1]}"
    }elsif ($path =~ m/Syntax\./) {
      print "subgraph cluster_syntax { \"$path$src\"[label=\"$src\",fillcolor=2,fontcolor=white]}"
    }elsif ($path =~ m/LogicalRelation\./) {
      print "subgraph cluster_logrel { \"$path$src\"[label=\"$src\",fillcolor=3]}"
    }elsif ($path =~ m/Validity\./) {
      print "subgraph cluster_subst { \"$path$src\"[label=\"$src\",fillcolor=4,fontcolor=white]}"
    }elsif ($path =~ m/TypingProperties\./) {
      print "subgraph cluster_typing { \"$path$src\"[label=\"$src\",fillcolor=5]}"
    }elsif ($path =~ m/Algorithmic\./) {
      print "subgraph cluster_algo { \"$path$src\"[label=\"$src\",fillcolor=9]}"
    }elsif ($path =~ m/Decidability\./) {
      print "subgraph cluster_dec { \"$path$src\"[label=\"$src\",fillcolor=10,fontcolor=white]}"
    }else {
      print "\"$path$src\"[label=\"$src\",fillcolor=6,fontcolor=white]"
    }
    for my $dest (split(" ", $dests)) {
      $dest =~ s/\//\./g ;
      print "  \"$1\" -> \"$path$src\";\n" if ($dest =~ m/theories\.(.*)\.vo/);
    }
  }
}
print "}\n";