module IRW.Libs.Data.String.Extra

import public Data.String

%default total

||| Concatenates a `List` of strings using the given separator.
export
listSep : (sep : String) -> List String -> String
listSep sep = fastConcat . intersperse sep

||| Concatenates a `SnocList` of strings using the given separator.
export
snocSep : (sep : String) -> SnocList String -> String
snocSep sep = listSep sep . (<>> [])

export
lowerFirst : String -> Bool
lowerFirst s =
  case strM s of
    StrCons c _ => isLower c
    StrNil      => False
