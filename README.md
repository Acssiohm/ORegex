# OCaml Regex Engine
## Installation
It's just a single OCaml file with no libraries used, so you can copy it or clone
and then use it with 
`utop
#use "main.ml";;`
or compile it.

## Features
### Supported actions
list : match , capture
Descriptions :
- match : you can search for a pattern re within a text txt with
    `recognizer re txt`
    or
    `recognize (compile_regex re) txt`
- match with captures : you can search for a pattern re that contains captures
  within a text txt with :
  `capturer re txt`
  or
  `capture (compile_regex re) txt`
### Supported regex syntax
This section can also be used as a cheatsheet for regex supported here
quick list : *, +, [...], ^, $, (...), ?, [^...], \s,\S,\d,\D,\w,\W,.,|
currently not supported : \b,\B,(^...), ..etc (non exhaustive, to be completed)
