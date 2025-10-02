def joinStringsWith (a : String) (b : String) (c : String) : String :=
String.append b (String.append a c)

joinStringsWith ", " "one" "and another"
