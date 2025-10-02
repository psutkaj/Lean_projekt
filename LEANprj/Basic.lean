import Mathlib

def joinStringsWith (a : String) (b : String) (c : String) : String :=
  String.append b (String.append a c)

#eval joinStringsWith ", " "one" "and another"
