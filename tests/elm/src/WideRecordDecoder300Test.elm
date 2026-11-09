module WideRecordDecoder300Test exposing (main)

{-| A 300-field record alias, used as a constructor function, can be filled in one
argument at a time by an `andMap` pipeline over `Maybe`.

`andMap` is defined here and applies a `Just` function to a `Just` argument. The
fields cycle through `Int`, `Float`, `Char`, `String` and `Bool`, and the test
reads back fields 0, 19, 20, 31, 32, 63, 64, 95, 96, 255, 256 and 299.
The local `mapMaybe` reads each field inside the `Maybe`.

-}

-- TAGS: elm-spec, sm-typbind-record, dm-typbind, d-app-basic-partial, d-app-basic-apply
-- CHECK: f0000: Just 1000
-- CHECK: f0019: Just False
-- CHECK: f0020: Just 1020
-- CHECK: f0031: Just 31.5
-- CHECK: f0032: Just 'g'
-- CHECK: f0063: Just "63s"
-- CHECK: f0064: Just True
-- CHECK: f0095: Just 1095
-- CHECK: f0096: Just 96.5
-- CHECK: f0255: Just 1255
-- CHECK: f0256: Just 256.5
-- CHECK: f0299: Just False

import Html exposing (text)

type alias R =
    { f0000 : Int
    , f0001 : Float
    , f0002 : Char
    , f0003 : String
    , f0004 : Bool
    , f0005 : Int
    , f0006 : Float
    , f0007 : Char
    , f0008 : String
    , f0009 : Bool
    , f0010 : Int
    , f0011 : Float
    , f0012 : Char
    , f0013 : String
    , f0014 : Bool
    , f0015 : Int
    , f0016 : Float
    , f0017 : Char
    , f0018 : String
    , f0019 : Bool
    , f0020 : Int
    , f0021 : Float
    , f0022 : Char
    , f0023 : String
    , f0024 : Bool
    , f0025 : Int
    , f0026 : Float
    , f0027 : Char
    , f0028 : String
    , f0029 : Bool
    , f0030 : Int
    , f0031 : Float
    , f0032 : Char
    , f0033 : String
    , f0034 : Bool
    , f0035 : Int
    , f0036 : Float
    , f0037 : Char
    , f0038 : String
    , f0039 : Bool
    , f0040 : Int
    , f0041 : Float
    , f0042 : Char
    , f0043 : String
    , f0044 : Bool
    , f0045 : Int
    , f0046 : Float
    , f0047 : Char
    , f0048 : String
    , f0049 : Bool
    , f0050 : Int
    , f0051 : Float
    , f0052 : Char
    , f0053 : String
    , f0054 : Bool
    , f0055 : Int
    , f0056 : Float
    , f0057 : Char
    , f0058 : String
    , f0059 : Bool
    , f0060 : Int
    , f0061 : Float
    , f0062 : Char
    , f0063 : String
    , f0064 : Bool
    , f0065 : Int
    , f0066 : Float
    , f0067 : Char
    , f0068 : String
    , f0069 : Bool
    , f0070 : Int
    , f0071 : Float
    , f0072 : Char
    , f0073 : String
    , f0074 : Bool
    , f0075 : Int
    , f0076 : Float
    , f0077 : Char
    , f0078 : String
    , f0079 : Bool
    , f0080 : Int
    , f0081 : Float
    , f0082 : Char
    , f0083 : String
    , f0084 : Bool
    , f0085 : Int
    , f0086 : Float
    , f0087 : Char
    , f0088 : String
    , f0089 : Bool
    , f0090 : Int
    , f0091 : Float
    , f0092 : Char
    , f0093 : String
    , f0094 : Bool
    , f0095 : Int
    , f0096 : Float
    , f0097 : Char
    , f0098 : String
    , f0099 : Bool
    , f0100 : Int
    , f0101 : Float
    , f0102 : Char
    , f0103 : String
    , f0104 : Bool
    , f0105 : Int
    , f0106 : Float
    , f0107 : Char
    , f0108 : String
    , f0109 : Bool
    , f0110 : Int
    , f0111 : Float
    , f0112 : Char
    , f0113 : String
    , f0114 : Bool
    , f0115 : Int
    , f0116 : Float
    , f0117 : Char
    , f0118 : String
    , f0119 : Bool
    , f0120 : Int
    , f0121 : Float
    , f0122 : Char
    , f0123 : String
    , f0124 : Bool
    , f0125 : Int
    , f0126 : Float
    , f0127 : Char
    , f0128 : String
    , f0129 : Bool
    , f0130 : Int
    , f0131 : Float
    , f0132 : Char
    , f0133 : String
    , f0134 : Bool
    , f0135 : Int
    , f0136 : Float
    , f0137 : Char
    , f0138 : String
    , f0139 : Bool
    , f0140 : Int
    , f0141 : Float
    , f0142 : Char
    , f0143 : String
    , f0144 : Bool
    , f0145 : Int
    , f0146 : Float
    , f0147 : Char
    , f0148 : String
    , f0149 : Bool
    , f0150 : Int
    , f0151 : Float
    , f0152 : Char
    , f0153 : String
    , f0154 : Bool
    , f0155 : Int
    , f0156 : Float
    , f0157 : Char
    , f0158 : String
    , f0159 : Bool
    , f0160 : Int
    , f0161 : Float
    , f0162 : Char
    , f0163 : String
    , f0164 : Bool
    , f0165 : Int
    , f0166 : Float
    , f0167 : Char
    , f0168 : String
    , f0169 : Bool
    , f0170 : Int
    , f0171 : Float
    , f0172 : Char
    , f0173 : String
    , f0174 : Bool
    , f0175 : Int
    , f0176 : Float
    , f0177 : Char
    , f0178 : String
    , f0179 : Bool
    , f0180 : Int
    , f0181 : Float
    , f0182 : Char
    , f0183 : String
    , f0184 : Bool
    , f0185 : Int
    , f0186 : Float
    , f0187 : Char
    , f0188 : String
    , f0189 : Bool
    , f0190 : Int
    , f0191 : Float
    , f0192 : Char
    , f0193 : String
    , f0194 : Bool
    , f0195 : Int
    , f0196 : Float
    , f0197 : Char
    , f0198 : String
    , f0199 : Bool
    , f0200 : Int
    , f0201 : Float
    , f0202 : Char
    , f0203 : String
    , f0204 : Bool
    , f0205 : Int
    , f0206 : Float
    , f0207 : Char
    , f0208 : String
    , f0209 : Bool
    , f0210 : Int
    , f0211 : Float
    , f0212 : Char
    , f0213 : String
    , f0214 : Bool
    , f0215 : Int
    , f0216 : Float
    , f0217 : Char
    , f0218 : String
    , f0219 : Bool
    , f0220 : Int
    , f0221 : Float
    , f0222 : Char
    , f0223 : String
    , f0224 : Bool
    , f0225 : Int
    , f0226 : Float
    , f0227 : Char
    , f0228 : String
    , f0229 : Bool
    , f0230 : Int
    , f0231 : Float
    , f0232 : Char
    , f0233 : String
    , f0234 : Bool
    , f0235 : Int
    , f0236 : Float
    , f0237 : Char
    , f0238 : String
    , f0239 : Bool
    , f0240 : Int
    , f0241 : Float
    , f0242 : Char
    , f0243 : String
    , f0244 : Bool
    , f0245 : Int
    , f0246 : Float
    , f0247 : Char
    , f0248 : String
    , f0249 : Bool
    , f0250 : Int
    , f0251 : Float
    , f0252 : Char
    , f0253 : String
    , f0254 : Bool
    , f0255 : Int
    , f0256 : Float
    , f0257 : Char
    , f0258 : String
    , f0259 : Bool
    , f0260 : Int
    , f0261 : Float
    , f0262 : Char
    , f0263 : String
    , f0264 : Bool
    , f0265 : Int
    , f0266 : Float
    , f0267 : Char
    , f0268 : String
    , f0269 : Bool
    , f0270 : Int
    , f0271 : Float
    , f0272 : Char
    , f0273 : String
    , f0274 : Bool
    , f0275 : Int
    , f0276 : Float
    , f0277 : Char
    , f0278 : String
    , f0279 : Bool
    , f0280 : Int
    , f0281 : Float
    , f0282 : Char
    , f0283 : String
    , f0284 : Bool
    , f0285 : Int
    , f0286 : Float
    , f0287 : Char
    , f0288 : String
    , f0289 : Bool
    , f0290 : Int
    , f0291 : Float
    , f0292 : Char
    , f0293 : String
    , f0294 : Bool
    , f0295 : Int
    , f0296 : Float
    , f0297 : Char
    , f0298 : String
    , f0299 : Bool
    }


andMap : Maybe a -> Maybe (a -> b) -> Maybe b
andMap ma mf =
    case ( mf, ma ) of
        ( Just f, Just a ) ->
            Just (f a)

        _ ->
            Nothing


mapMaybe : (a -> b) -> Maybe a -> Maybe b
mapMaybe f ma =
    case ma of
        Just a ->
            Just (f a)

        Nothing ->
            Nothing


build : Int -> Maybe R
build b =
    Just R
        |> andMap (Just (b + 999))
        |> andMap (Just (toFloat b + 1.5 - 1))
        |> andMap (Just ((if b == 1 then 'c' else '?')))
        |> andMap (Just ((if b == 1 then "3s" else "?")))
        |> andMap (Just (modBy 2 (b + 3) == 0))
        |> andMap (Just (b + 1004))
        |> andMap (Just (toFloat b + 6.5 - 1))
        |> andMap (Just ((if b == 1 then 'h' else '?')))
        |> andMap (Just ((if b == 1 then "8s" else "?")))
        |> andMap (Just (modBy 2 (b + 8) == 0))
        |> andMap (Just (b + 1009))
        |> andMap (Just (toFloat b + 11.5 - 1))
        |> andMap (Just ((if b == 1 then 'm' else '?')))
        |> andMap (Just ((if b == 1 then "13s" else "?")))
        |> andMap (Just (modBy 2 (b + 13) == 0))
        |> andMap (Just (b + 1014))
        |> andMap (Just (toFloat b + 16.5 - 1))
        |> andMap (Just ((if b == 1 then 'r' else '?')))
        |> andMap (Just ((if b == 1 then "18s" else "?")))
        |> andMap (Just (modBy 2 (b + 18) == 0))
        |> andMap (Just (b + 1019))
        |> andMap (Just (toFloat b + 21.5 - 1))
        |> andMap (Just ((if b == 1 then 'w' else '?')))
        |> andMap (Just ((if b == 1 then "23s" else "?")))
        |> andMap (Just (modBy 2 (b + 23) == 0))
        |> andMap (Just (b + 1024))
        |> andMap (Just (toFloat b + 26.5 - 1))
        |> andMap (Just ((if b == 1 then 'b' else '?')))
        |> andMap (Just ((if b == 1 then "28s" else "?")))
        |> andMap (Just (modBy 2 (b + 28) == 0))
        |> andMap (Just (b + 1029))
        |> andMap (Just (toFloat b + 31.5 - 1))
        |> andMap (Just ((if b == 1 then 'g' else '?')))
        |> andMap (Just ((if b == 1 then "33s" else "?")))
        |> andMap (Just (modBy 2 (b + 33) == 0))
        |> andMap (Just (b + 1034))
        |> andMap (Just (toFloat b + 36.5 - 1))
        |> andMap (Just ((if b == 1 then 'l' else '?')))
        |> andMap (Just ((if b == 1 then "38s" else "?")))
        |> andMap (Just (modBy 2 (b + 38) == 0))
        |> andMap (Just (b + 1039))
        |> andMap (Just (toFloat b + 41.5 - 1))
        |> andMap (Just ((if b == 1 then 'q' else '?')))
        |> andMap (Just ((if b == 1 then "43s" else "?")))
        |> andMap (Just (modBy 2 (b + 43) == 0))
        |> andMap (Just (b + 1044))
        |> andMap (Just (toFloat b + 46.5 - 1))
        |> andMap (Just ((if b == 1 then 'v' else '?')))
        |> andMap (Just ((if b == 1 then "48s" else "?")))
        |> andMap (Just (modBy 2 (b + 48) == 0))
        |> andMap (Just (b + 1049))
        |> andMap (Just (toFloat b + 51.5 - 1))
        |> andMap (Just ((if b == 1 then 'a' else '?')))
        |> andMap (Just ((if b == 1 then "53s" else "?")))
        |> andMap (Just (modBy 2 (b + 53) == 0))
        |> andMap (Just (b + 1054))
        |> andMap (Just (toFloat b + 56.5 - 1))
        |> andMap (Just ((if b == 1 then 'f' else '?')))
        |> andMap (Just ((if b == 1 then "58s" else "?")))
        |> andMap (Just (modBy 2 (b + 58) == 0))
        |> andMap (Just (b + 1059))
        |> andMap (Just (toFloat b + 61.5 - 1))
        |> andMap (Just ((if b == 1 then 'k' else '?')))
        |> andMap (Just ((if b == 1 then "63s" else "?")))
        |> andMap (Just (modBy 2 (b + 63) == 0))
        |> andMap (Just (b + 1064))
        |> andMap (Just (toFloat b + 66.5 - 1))
        |> andMap (Just ((if b == 1 then 'p' else '?')))
        |> andMap (Just ((if b == 1 then "68s" else "?")))
        |> andMap (Just (modBy 2 (b + 68) == 0))
        |> andMap (Just (b + 1069))
        |> andMap (Just (toFloat b + 71.5 - 1))
        |> andMap (Just ((if b == 1 then 'u' else '?')))
        |> andMap (Just ((if b == 1 then "73s" else "?")))
        |> andMap (Just (modBy 2 (b + 73) == 0))
        |> andMap (Just (b + 1074))
        |> andMap (Just (toFloat b + 76.5 - 1))
        |> andMap (Just ((if b == 1 then 'z' else '?')))
        |> andMap (Just ((if b == 1 then "78s" else "?")))
        |> andMap (Just (modBy 2 (b + 78) == 0))
        |> andMap (Just (b + 1079))
        |> andMap (Just (toFloat b + 81.5 - 1))
        |> andMap (Just ((if b == 1 then 'e' else '?')))
        |> andMap (Just ((if b == 1 then "83s" else "?")))
        |> andMap (Just (modBy 2 (b + 83) == 0))
        |> andMap (Just (b + 1084))
        |> andMap (Just (toFloat b + 86.5 - 1))
        |> andMap (Just ((if b == 1 then 'j' else '?')))
        |> andMap (Just ((if b == 1 then "88s" else "?")))
        |> andMap (Just (modBy 2 (b + 88) == 0))
        |> andMap (Just (b + 1089))
        |> andMap (Just (toFloat b + 91.5 - 1))
        |> andMap (Just ((if b == 1 then 'o' else '?')))
        |> andMap (Just ((if b == 1 then "93s" else "?")))
        |> andMap (Just (modBy 2 (b + 93) == 0))
        |> andMap (Just (b + 1094))
        |> andMap (Just (toFloat b + 96.5 - 1))
        |> andMap (Just ((if b == 1 then 't' else '?')))
        |> andMap (Just ((if b == 1 then "98s" else "?")))
        |> andMap (Just (modBy 2 (b + 98) == 0))
        |> andMap (Just (b + 1099))
        |> andMap (Just (toFloat b + 101.5 - 1))
        |> andMap (Just ((if b == 1 then 'y' else '?')))
        |> andMap (Just ((if b == 1 then "103s" else "?")))
        |> andMap (Just (modBy 2 (b + 103) == 0))
        |> andMap (Just (b + 1104))
        |> andMap (Just (toFloat b + 106.5 - 1))
        |> andMap (Just ((if b == 1 then 'd' else '?')))
        |> andMap (Just ((if b == 1 then "108s" else "?")))
        |> andMap (Just (modBy 2 (b + 108) == 0))
        |> andMap (Just (b + 1109))
        |> andMap (Just (toFloat b + 111.5 - 1))
        |> andMap (Just ((if b == 1 then 'i' else '?')))
        |> andMap (Just ((if b == 1 then "113s" else "?")))
        |> andMap (Just (modBy 2 (b + 113) == 0))
        |> andMap (Just (b + 1114))
        |> andMap (Just (toFloat b + 116.5 - 1))
        |> andMap (Just ((if b == 1 then 'n' else '?')))
        |> andMap (Just ((if b == 1 then "118s" else "?")))
        |> andMap (Just (modBy 2 (b + 118) == 0))
        |> andMap (Just (b + 1119))
        |> andMap (Just (toFloat b + 121.5 - 1))
        |> andMap (Just ((if b == 1 then 's' else '?')))
        |> andMap (Just ((if b == 1 then "123s" else "?")))
        |> andMap (Just (modBy 2 (b + 123) == 0))
        |> andMap (Just (b + 1124))
        |> andMap (Just (toFloat b + 126.5 - 1))
        |> andMap (Just ((if b == 1 then 'x' else '?')))
        |> andMap (Just ((if b == 1 then "128s" else "?")))
        |> andMap (Just (modBy 2 (b + 128) == 0))
        |> andMap (Just (b + 1129))
        |> andMap (Just (toFloat b + 131.5 - 1))
        |> andMap (Just ((if b == 1 then 'c' else '?')))
        |> andMap (Just ((if b == 1 then "133s" else "?")))
        |> andMap (Just (modBy 2 (b + 133) == 0))
        |> andMap (Just (b + 1134))
        |> andMap (Just (toFloat b + 136.5 - 1))
        |> andMap (Just ((if b == 1 then 'h' else '?')))
        |> andMap (Just ((if b == 1 then "138s" else "?")))
        |> andMap (Just (modBy 2 (b + 138) == 0))
        |> andMap (Just (b + 1139))
        |> andMap (Just (toFloat b + 141.5 - 1))
        |> andMap (Just ((if b == 1 then 'm' else '?')))
        |> andMap (Just ((if b == 1 then "143s" else "?")))
        |> andMap (Just (modBy 2 (b + 143) == 0))
        |> andMap (Just (b + 1144))
        |> andMap (Just (toFloat b + 146.5 - 1))
        |> andMap (Just ((if b == 1 then 'r' else '?')))
        |> andMap (Just ((if b == 1 then "148s" else "?")))
        |> andMap (Just (modBy 2 (b + 148) == 0))
        |> andMap (Just (b + 1149))
        |> andMap (Just (toFloat b + 151.5 - 1))
        |> andMap (Just ((if b == 1 then 'w' else '?')))
        |> andMap (Just ((if b == 1 then "153s" else "?")))
        |> andMap (Just (modBy 2 (b + 153) == 0))
        |> andMap (Just (b + 1154))
        |> andMap (Just (toFloat b + 156.5 - 1))
        |> andMap (Just ((if b == 1 then 'b' else '?')))
        |> andMap (Just ((if b == 1 then "158s" else "?")))
        |> andMap (Just (modBy 2 (b + 158) == 0))
        |> andMap (Just (b + 1159))
        |> andMap (Just (toFloat b + 161.5 - 1))
        |> andMap (Just ((if b == 1 then 'g' else '?')))
        |> andMap (Just ((if b == 1 then "163s" else "?")))
        |> andMap (Just (modBy 2 (b + 163) == 0))
        |> andMap (Just (b + 1164))
        |> andMap (Just (toFloat b + 166.5 - 1))
        |> andMap (Just ((if b == 1 then 'l' else '?')))
        |> andMap (Just ((if b == 1 then "168s" else "?")))
        |> andMap (Just (modBy 2 (b + 168) == 0))
        |> andMap (Just (b + 1169))
        |> andMap (Just (toFloat b + 171.5 - 1))
        |> andMap (Just ((if b == 1 then 'q' else '?')))
        |> andMap (Just ((if b == 1 then "173s" else "?")))
        |> andMap (Just (modBy 2 (b + 173) == 0))
        |> andMap (Just (b + 1174))
        |> andMap (Just (toFloat b + 176.5 - 1))
        |> andMap (Just ((if b == 1 then 'v' else '?')))
        |> andMap (Just ((if b == 1 then "178s" else "?")))
        |> andMap (Just (modBy 2 (b + 178) == 0))
        |> andMap (Just (b + 1179))
        |> andMap (Just (toFloat b + 181.5 - 1))
        |> andMap (Just ((if b == 1 then 'a' else '?')))
        |> andMap (Just ((if b == 1 then "183s" else "?")))
        |> andMap (Just (modBy 2 (b + 183) == 0))
        |> andMap (Just (b + 1184))
        |> andMap (Just (toFloat b + 186.5 - 1))
        |> andMap (Just ((if b == 1 then 'f' else '?')))
        |> andMap (Just ((if b == 1 then "188s" else "?")))
        |> andMap (Just (modBy 2 (b + 188) == 0))
        |> andMap (Just (b + 1189))
        |> andMap (Just (toFloat b + 191.5 - 1))
        |> andMap (Just ((if b == 1 then 'k' else '?')))
        |> andMap (Just ((if b == 1 then "193s" else "?")))
        |> andMap (Just (modBy 2 (b + 193) == 0))
        |> andMap (Just (b + 1194))
        |> andMap (Just (toFloat b + 196.5 - 1))
        |> andMap (Just ((if b == 1 then 'p' else '?')))
        |> andMap (Just ((if b == 1 then "198s" else "?")))
        |> andMap (Just (modBy 2 (b + 198) == 0))
        |> andMap (Just (b + 1199))
        |> andMap (Just (toFloat b + 201.5 - 1))
        |> andMap (Just ((if b == 1 then 'u' else '?')))
        |> andMap (Just ((if b == 1 then "203s" else "?")))
        |> andMap (Just (modBy 2 (b + 203) == 0))
        |> andMap (Just (b + 1204))
        |> andMap (Just (toFloat b + 206.5 - 1))
        |> andMap (Just ((if b == 1 then 'z' else '?')))
        |> andMap (Just ((if b == 1 then "208s" else "?")))
        |> andMap (Just (modBy 2 (b + 208) == 0))
        |> andMap (Just (b + 1209))
        |> andMap (Just (toFloat b + 211.5 - 1))
        |> andMap (Just ((if b == 1 then 'e' else '?')))
        |> andMap (Just ((if b == 1 then "213s" else "?")))
        |> andMap (Just (modBy 2 (b + 213) == 0))
        |> andMap (Just (b + 1214))
        |> andMap (Just (toFloat b + 216.5 - 1))
        |> andMap (Just ((if b == 1 then 'j' else '?')))
        |> andMap (Just ((if b == 1 then "218s" else "?")))
        |> andMap (Just (modBy 2 (b + 218) == 0))
        |> andMap (Just (b + 1219))
        |> andMap (Just (toFloat b + 221.5 - 1))
        |> andMap (Just ((if b == 1 then 'o' else '?')))
        |> andMap (Just ((if b == 1 then "223s" else "?")))
        |> andMap (Just (modBy 2 (b + 223) == 0))
        |> andMap (Just (b + 1224))
        |> andMap (Just (toFloat b + 226.5 - 1))
        |> andMap (Just ((if b == 1 then 't' else '?')))
        |> andMap (Just ((if b == 1 then "228s" else "?")))
        |> andMap (Just (modBy 2 (b + 228) == 0))
        |> andMap (Just (b + 1229))
        |> andMap (Just (toFloat b + 231.5 - 1))
        |> andMap (Just ((if b == 1 then 'y' else '?')))
        |> andMap (Just ((if b == 1 then "233s" else "?")))
        |> andMap (Just (modBy 2 (b + 233) == 0))
        |> andMap (Just (b + 1234))
        |> andMap (Just (toFloat b + 236.5 - 1))
        |> andMap (Just ((if b == 1 then 'd' else '?')))
        |> andMap (Just ((if b == 1 then "238s" else "?")))
        |> andMap (Just (modBy 2 (b + 238) == 0))
        |> andMap (Just (b + 1239))
        |> andMap (Just (toFloat b + 241.5 - 1))
        |> andMap (Just ((if b == 1 then 'i' else '?')))
        |> andMap (Just ((if b == 1 then "243s" else "?")))
        |> andMap (Just (modBy 2 (b + 243) == 0))
        |> andMap (Just (b + 1244))
        |> andMap (Just (toFloat b + 246.5 - 1))
        |> andMap (Just ((if b == 1 then 'n' else '?')))
        |> andMap (Just ((if b == 1 then "248s" else "?")))
        |> andMap (Just (modBy 2 (b + 248) == 0))
        |> andMap (Just (b + 1249))
        |> andMap (Just (toFloat b + 251.5 - 1))
        |> andMap (Just ((if b == 1 then 's' else '?')))
        |> andMap (Just ((if b == 1 then "253s" else "?")))
        |> andMap (Just (modBy 2 (b + 253) == 0))
        |> andMap (Just (b + 1254))
        |> andMap (Just (toFloat b + 256.5 - 1))
        |> andMap (Just ((if b == 1 then 'x' else '?')))
        |> andMap (Just ((if b == 1 then "258s" else "?")))
        |> andMap (Just (modBy 2 (b + 258) == 0))
        |> andMap (Just (b + 1259))
        |> andMap (Just (toFloat b + 261.5 - 1))
        |> andMap (Just ((if b == 1 then 'c' else '?')))
        |> andMap (Just ((if b == 1 then "263s" else "?")))
        |> andMap (Just (modBy 2 (b + 263) == 0))
        |> andMap (Just (b + 1264))
        |> andMap (Just (toFloat b + 266.5 - 1))
        |> andMap (Just ((if b == 1 then 'h' else '?')))
        |> andMap (Just ((if b == 1 then "268s" else "?")))
        |> andMap (Just (modBy 2 (b + 268) == 0))
        |> andMap (Just (b + 1269))
        |> andMap (Just (toFloat b + 271.5 - 1))
        |> andMap (Just ((if b == 1 then 'm' else '?')))
        |> andMap (Just ((if b == 1 then "273s" else "?")))
        |> andMap (Just (modBy 2 (b + 273) == 0))
        |> andMap (Just (b + 1274))
        |> andMap (Just (toFloat b + 276.5 - 1))
        |> andMap (Just ((if b == 1 then 'r' else '?')))
        |> andMap (Just ((if b == 1 then "278s" else "?")))
        |> andMap (Just (modBy 2 (b + 278) == 0))
        |> andMap (Just (b + 1279))
        |> andMap (Just (toFloat b + 281.5 - 1))
        |> andMap (Just ((if b == 1 then 'w' else '?')))
        |> andMap (Just ((if b == 1 then "283s" else "?")))
        |> andMap (Just (modBy 2 (b + 283) == 0))
        |> andMap (Just (b + 1284))
        |> andMap (Just (toFloat b + 286.5 - 1))
        |> andMap (Just ((if b == 1 then 'b' else '?')))
        |> andMap (Just ((if b == 1 then "288s" else "?")))
        |> andMap (Just (modBy 2 (b + 288) == 0))
        |> andMap (Just (b + 1289))
        |> andMap (Just (toFloat b + 291.5 - 1))
        |> andMap (Just ((if b == 1 then 'g' else '?')))
        |> andMap (Just ((if b == 1 then "293s" else "?")))
        |> andMap (Just (modBy 2 (b + 293) == 0))
        |> andMap (Just (b + 1294))
        |> andMap (Just (toFloat b + 296.5 - 1))
        |> andMap (Just ((if b == 1 then 'l' else '?')))
        |> andMap (Just ((if b == 1 then "298s" else "?")))
        |> andMap (Just (modBy 2 (b + 298) == 0))


main =
    let
        base =
            1 + (Char.toCode 'b' - Char.toCode 'a') - 1

        r =
            build base

        _ =
            Debug.log "f0000" (mapMaybe .f0000 r)

        _ =
            Debug.log "f0019" (mapMaybe .f0019 r)

        _ =
            Debug.log "f0020" (mapMaybe .f0020 r)

        _ =
            Debug.log "f0031" (mapMaybe .f0031 r)

        _ =
            Debug.log "f0032" (mapMaybe .f0032 r)

        _ =
            Debug.log "f0063" (mapMaybe .f0063 r)

        _ =
            Debug.log "f0064" (mapMaybe .f0064 r)

        _ =
            Debug.log "f0095" (mapMaybe .f0095 r)

        _ =
            Debug.log "f0096" (mapMaybe .f0096 r)

        _ =
            Debug.log "f0255" (mapMaybe .f0255 r)

        _ =
            Debug.log "f0256" (mapMaybe .f0256 r)

        _ =
            Debug.log "f0299" (mapMaybe .f0299 r)

    in
    text "done"
