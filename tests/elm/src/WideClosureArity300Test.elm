module WideClosureArity300Test exposing (main)

{-| A function of 300 parameters of mixed types can be partially applied in seven
stages and gives the right result once the last argument is supplied.

`big` takes `Int`, `Float`, `Char`, `String` and `Bool` arguments and returns an
`Int`; it scores each `String` argument by comparing it with the literal expected
at that position. Starting from the list `[ big ]`, `main` maps `step0` to
`step6` over it in turn with a local `map`, supplying 1, 7, 20, 63, 64, 65 and 80
arguments. Every list but the last holds a partially applied function; the last
holds the result, `[1882518]`.

-}

-- TAGS: elm-spec, d-exp-lambda, d-app-closure
-- CHECK: res: [1882518]

import Html exposing (text)

big : Int -> Float -> Char -> String -> Bool -> Int -> Float -> Char -> String -> Bool -> Int -> Float -> Char -> String -> Bool -> Int -> Float -> Char -> String -> Bool -> Int -> Float -> Char -> String -> Bool -> Int -> Float -> Char -> String -> Bool -> Int -> Float -> Char -> String -> Bool -> Int -> Float -> Char -> String -> Bool -> Int -> Float -> Char -> String -> Bool -> Int -> Float -> Char -> String -> Bool -> Int -> Float -> Char -> String -> Bool -> Int -> Float -> Char -> String -> Bool -> Int -> Float -> Char -> String -> Bool -> Int -> Float -> Char -> String -> Bool -> Int -> Float -> Char -> String -> Bool -> Int -> Float -> Char -> String -> Bool -> Int -> Float -> Char -> String -> Bool -> Int -> Float -> Char -> String -> Bool -> Int -> Float -> Char -> String -> Bool -> Int -> Float -> Char -> String -> Bool -> Int -> Float -> Char -> String -> Bool -> Int -> Float -> Char -> String -> Bool -> Int -> Float -> Char -> String -> Bool -> Int -> Float -> Char -> String -> Bool -> Int -> Float -> Char -> String -> Bool -> Int -> Float -> Char -> String -> Bool -> Int -> Float -> Char -> String -> Bool -> Int -> Float -> Char -> String -> Bool -> Int -> Float -> Char -> String -> Bool -> Int -> Float -> Char -> String -> Bool -> Int -> Float -> Char -> String -> Bool -> Int -> Float -> Char -> String -> Bool -> Int -> Float -> Char -> String -> Bool -> Int -> Float -> Char -> String -> Bool -> Int -> Float -> Char -> String -> Bool -> Int -> Float -> Char -> String -> Bool -> Int -> Float -> Char -> String -> Bool -> Int -> Float -> Char -> String -> Bool -> Int -> Float -> Char -> String -> Bool -> Int -> Float -> Char -> String -> Bool -> Int -> Float -> Char -> String -> Bool -> Int -> Float -> Char -> String -> Bool -> Int -> Float -> Char -> String -> Bool -> Int -> Float -> Char -> String -> Bool -> Int -> Float -> Char -> String -> Bool -> Int -> Float -> Char -> String -> Bool -> Int -> Float -> Char -> String -> Bool -> Int -> Float -> Char -> String -> Bool -> Int -> Float -> Char -> String -> Bool -> Int -> Float -> Char -> String -> Bool -> Int -> Float -> Char -> String -> Bool -> Int -> Float -> Char -> String -> Bool -> Int -> Float -> Char -> String -> Bool -> Int -> Float -> Char -> String -> Bool -> Int -> Float -> Char -> String -> Bool -> Int -> Float -> Char -> String -> Bool -> Int -> Float -> Char -> String -> Bool -> Int -> Float -> Char -> String -> Bool -> Int -> Float -> Char -> String -> Bool -> Int -> Float -> Char -> String -> Bool -> Int
big a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37 a38 a39 a40 a41 a42 a43 a44 a45 a46 a47 a48 a49 a50 a51 a52 a53 a54 a55 a56 a57 a58 a59 a60 a61 a62 a63 a64 a65 a66 a67 a68 a69 a70 a71 a72 a73 a74 a75 a76 a77 a78 a79 a80 a81 a82 a83 a84 a85 a86 a87 a88 a89 a90 a91 a92 a93 a94 a95 a96 a97 a98 a99 a100 a101 a102 a103 a104 a105 a106 a107 a108 a109 a110 a111 a112 a113 a114 a115 a116 a117 a118 a119 a120 a121 a122 a123 a124 a125 a126 a127 a128 a129 a130 a131 a132 a133 a134 a135 a136 a137 a138 a139 a140 a141 a142 a143 a144 a145 a146 a147 a148 a149 a150 a151 a152 a153 a154 a155 a156 a157 a158 a159 a160 a161 a162 a163 a164 a165 a166 a167 a168 a169 a170 a171 a172 a173 a174 a175 a176 a177 a178 a179 a180 a181 a182 a183 a184 a185 a186 a187 a188 a189 a190 a191 a192 a193 a194 a195 a196 a197 a198 a199 a200 a201 a202 a203 a204 a205 a206 a207 a208 a209 a210 a211 a212 a213 a214 a215 a216 a217 a218 a219 a220 a221 a222 a223 a224 a225 a226 a227 a228 a229 a230 a231 a232 a233 a234 a235 a236 a237 a238 a239 a240 a241 a242 a243 a244 a245 a246 a247 a248 a249 a250 a251 a252 a253 a254 a255 a256 a257 a258 a259 a260 a261 a262 a263 a264 a265 a266 a267 a268 a269 a270 a271 a272 a273 a274 a275 a276 a277 a278 a279 a280 a281 a282 a283 a284 a285 a286 a287 a288 a289 a290 a291 a292 a293 a294 a295 a296 a297 a298 a299 =
    a0 * 1
    + round (a1 * 10)
    + Char.toCode a2
    + (if a3 == "s3" then 4 else 0)
    + (if a4 then 4 else 0)
    + a5 * 6
    + round (a6 * 10)
    + Char.toCode a7
    + (if a8 == "s8" then 9 else 0)
    + (if a9 then 9 else 0)
    + a10 * 11
    + round (a11 * 10)
    + Char.toCode a12
    + (if a13 == "s13" then 14 else 0)
    + (if a14 then 14 else 0)
    + a15 * 16
    + round (a16 * 10)
    + Char.toCode a17
    + (if a18 == "s18" then 19 else 0)
    + (if a19 then 19 else 0)
    + a20 * 21
    + round (a21 * 10)
    + Char.toCode a22
    + (if a23 == "s23" then 24 else 0)
    + (if a24 then 24 else 0)
    + a25 * 26
    + round (a26 * 10)
    + Char.toCode a27
    + (if a28 == "s28" then 29 else 0)
    + (if a29 then 29 else 0)
    + a30 * 31
    + round (a31 * 10)
    + Char.toCode a32
    + (if a33 == "s33" then 34 else 0)
    + (if a34 then 34 else 0)
    + a35 * 36
    + round (a36 * 10)
    + Char.toCode a37
    + (if a38 == "s38" then 39 else 0)
    + (if a39 then 39 else 0)
    + a40 * 41
    + round (a41 * 10)
    + Char.toCode a42
    + (if a43 == "s43" then 44 else 0)
    + (if a44 then 44 else 0)
    + a45 * 46
    + round (a46 * 10)
    + Char.toCode a47
    + (if a48 == "s48" then 49 else 0)
    + (if a49 then 49 else 0)
    + a50 * 51
    + round (a51 * 10)
    + Char.toCode a52
    + (if a53 == "s53" then 54 else 0)
    + (if a54 then 54 else 0)
    + a55 * 56
    + round (a56 * 10)
    + Char.toCode a57
    + (if a58 == "s58" then 59 else 0)
    + (if a59 then 59 else 0)
    + a60 * 61
    + round (a61 * 10)
    + Char.toCode a62
    + (if a63 == "s63" then 64 else 0)
    + (if a64 then 64 else 0)
    + a65 * 66
    + round (a66 * 10)
    + Char.toCode a67
    + (if a68 == "s68" then 69 else 0)
    + (if a69 then 69 else 0)
    + a70 * 71
    + round (a71 * 10)
    + Char.toCode a72
    + (if a73 == "s73" then 74 else 0)
    + (if a74 then 74 else 0)
    + a75 * 76
    + round (a76 * 10)
    + Char.toCode a77
    + (if a78 == "s78" then 79 else 0)
    + (if a79 then 79 else 0)
    + a80 * 81
    + round (a81 * 10)
    + Char.toCode a82
    + (if a83 == "s83" then 84 else 0)
    + (if a84 then 84 else 0)
    + a85 * 86
    + round (a86 * 10)
    + Char.toCode a87
    + (if a88 == "s88" then 89 else 0)
    + (if a89 then 89 else 0)
    + a90 * 91
    + round (a91 * 10)
    + Char.toCode a92
    + (if a93 == "s93" then 94 else 0)
    + (if a94 then 94 else 0)
    + a95 * 96
    + round (a96 * 10)
    + Char.toCode a97
    + (if a98 == "s98" then 99 else 0)
    + (if a99 then 99 else 0)
    + a100 * 101
    + round (a101 * 10)
    + Char.toCode a102
    + (if a103 == "s103" then 104 else 0)
    + (if a104 then 104 else 0)
    + a105 * 106
    + round (a106 * 10)
    + Char.toCode a107
    + (if a108 == "s108" then 109 else 0)
    + (if a109 then 109 else 0)
    + a110 * 111
    + round (a111 * 10)
    + Char.toCode a112
    + (if a113 == "s113" then 114 else 0)
    + (if a114 then 114 else 0)
    + a115 * 116
    + round (a116 * 10)
    + Char.toCode a117
    + (if a118 == "s118" then 119 else 0)
    + (if a119 then 119 else 0)
    + a120 * 121
    + round (a121 * 10)
    + Char.toCode a122
    + (if a123 == "s123" then 124 else 0)
    + (if a124 then 124 else 0)
    + a125 * 126
    + round (a126 * 10)
    + Char.toCode a127
    + (if a128 == "s128" then 129 else 0)
    + (if a129 then 129 else 0)
    + a130 * 131
    + round (a131 * 10)
    + Char.toCode a132
    + (if a133 == "s133" then 134 else 0)
    + (if a134 then 134 else 0)
    + a135 * 136
    + round (a136 * 10)
    + Char.toCode a137
    + (if a138 == "s138" then 139 else 0)
    + (if a139 then 139 else 0)
    + a140 * 141
    + round (a141 * 10)
    + Char.toCode a142
    + (if a143 == "s143" then 144 else 0)
    + (if a144 then 144 else 0)
    + a145 * 146
    + round (a146 * 10)
    + Char.toCode a147
    + (if a148 == "s148" then 149 else 0)
    + (if a149 then 149 else 0)
    + a150 * 151
    + round (a151 * 10)
    + Char.toCode a152
    + (if a153 == "s153" then 154 else 0)
    + (if a154 then 154 else 0)
    + a155 * 156
    + round (a156 * 10)
    + Char.toCode a157
    + (if a158 == "s158" then 159 else 0)
    + (if a159 then 159 else 0)
    + a160 * 161
    + round (a161 * 10)
    + Char.toCode a162
    + (if a163 == "s163" then 164 else 0)
    + (if a164 then 164 else 0)
    + a165 * 166
    + round (a166 * 10)
    + Char.toCode a167
    + (if a168 == "s168" then 169 else 0)
    + (if a169 then 169 else 0)
    + a170 * 171
    + round (a171 * 10)
    + Char.toCode a172
    + (if a173 == "s173" then 174 else 0)
    + (if a174 then 174 else 0)
    + a175 * 176
    + round (a176 * 10)
    + Char.toCode a177
    + (if a178 == "s178" then 179 else 0)
    + (if a179 then 179 else 0)
    + a180 * 181
    + round (a181 * 10)
    + Char.toCode a182
    + (if a183 == "s183" then 184 else 0)
    + (if a184 then 184 else 0)
    + a185 * 186
    + round (a186 * 10)
    + Char.toCode a187
    + (if a188 == "s188" then 189 else 0)
    + (if a189 then 189 else 0)
    + a190 * 191
    + round (a191 * 10)
    + Char.toCode a192
    + (if a193 == "s193" then 194 else 0)
    + (if a194 then 194 else 0)
    + a195 * 196
    + round (a196 * 10)
    + Char.toCode a197
    + (if a198 == "s198" then 199 else 0)
    + (if a199 then 199 else 0)
    + a200 * 201
    + round (a201 * 10)
    + Char.toCode a202
    + (if a203 == "s203" then 204 else 0)
    + (if a204 then 204 else 0)
    + a205 * 206
    + round (a206 * 10)
    + Char.toCode a207
    + (if a208 == "s208" then 209 else 0)
    + (if a209 then 209 else 0)
    + a210 * 211
    + round (a211 * 10)
    + Char.toCode a212
    + (if a213 == "s213" then 214 else 0)
    + (if a214 then 214 else 0)
    + a215 * 216
    + round (a216 * 10)
    + Char.toCode a217
    + (if a218 == "s218" then 219 else 0)
    + (if a219 then 219 else 0)
    + a220 * 221
    + round (a221 * 10)
    + Char.toCode a222
    + (if a223 == "s223" then 224 else 0)
    + (if a224 then 224 else 0)
    + a225 * 226
    + round (a226 * 10)
    + Char.toCode a227
    + (if a228 == "s228" then 229 else 0)
    + (if a229 then 229 else 0)
    + a230 * 231
    + round (a231 * 10)
    + Char.toCode a232
    + (if a233 == "s233" then 234 else 0)
    + (if a234 then 234 else 0)
    + a235 * 236
    + round (a236 * 10)
    + Char.toCode a237
    + (if a238 == "s238" then 239 else 0)
    + (if a239 then 239 else 0)
    + a240 * 241
    + round (a241 * 10)
    + Char.toCode a242
    + (if a243 == "s243" then 244 else 0)
    + (if a244 then 244 else 0)
    + a245 * 246
    + round (a246 * 10)
    + Char.toCode a247
    + (if a248 == "s248" then 249 else 0)
    + (if a249 then 249 else 0)
    + a250 * 251
    + round (a251 * 10)
    + Char.toCode a252
    + (if a253 == "s253" then 254 else 0)
    + (if a254 then 254 else 0)
    + a255 * 256
    + round (a256 * 10)
    + Char.toCode a257
    + (if a258 == "s258" then 259 else 0)
    + (if a259 then 259 else 0)
    + a260 * 261
    + round (a261 * 10)
    + Char.toCode a262
    + (if a263 == "s263" then 264 else 0)
    + (if a264 then 264 else 0)
    + a265 * 266
    + round (a266 * 10)
    + Char.toCode a267
    + (if a268 == "s268" then 269 else 0)
    + (if a269 then 269 else 0)
    + a270 * 271
    + round (a271 * 10)
    + Char.toCode a272
    + (if a273 == "s273" then 274 else 0)
    + (if a274 then 274 else 0)
    + a275 * 276
    + round (a276 * 10)
    + Char.toCode a277
    + (if a278 == "s278" then 279 else 0)
    + (if a279 then 279 else 0)
    + a280 * 281
    + round (a281 * 10)
    + Char.toCode a282
    + (if a283 == "s283" then 284 else 0)
    + (if a284 then 284 else 0)
    + a285 * 286
    + round (a286 * 10)
    + Char.toCode a287
    + (if a288 == "s288" then 289 else 0)
    + (if a289 then 289 else 0)
    + a290 * 291
    + round (a291 * 10)
    + Char.toCode a292
    + (if a293 == "s293" then 294 else 0)
    + (if a294 then 294 else 0)
    + a295 * 296
    + round (a296 * 10)
    + Char.toCode a297
    + (if a298 == "s298" then 299 else 0)
    + (if a299 then 299 else 0)


step0 h b =
    h (b + 0)

step1 h b =
    h (toFloat b + 1.5 - 1) ((if b == 1 then 'c' else '?')) ((if b == 1 then "s3" else "?")) (modBy 2 (b + 3) == 0) (b + 5) (toFloat b + 6.5 - 1) ((if b == 1 then 'h' else '?'))

step2 h b =
    h ((if b == 1 then "s8" else "?")) (modBy 2 (b + 8) == 0) (b + 10) (toFloat b + 11.5 - 1) ((if b == 1 then 'm' else '?')) ((if b == 1 then "s13" else "?")) (modBy 2 (b + 13) == 0) (b + 15) (toFloat b + 16.5 - 1) ((if b == 1 then 'r' else '?')) ((if b == 1 then "s18" else "?")) (modBy 2 (b + 18) == 0) (b + 20) (toFloat b + 21.5 - 1) ((if b == 1 then 'w' else '?')) ((if b == 1 then "s23" else "?")) (modBy 2 (b + 23) == 0) (b + 25) (toFloat b + 26.5 - 1) ((if b == 1 then 'b' else '?'))

step3 h b =
    h ((if b == 1 then "s28" else "?")) (modBy 2 (b + 28) == 0) (b + 30) (toFloat b + 31.5 - 1) ((if b == 1 then 'g' else '?')) ((if b == 1 then "s33" else "?")) (modBy 2 (b + 33) == 0) (b + 35) (toFloat b + 36.5 - 1) ((if b == 1 then 'l' else '?')) ((if b == 1 then "s38" else "?")) (modBy 2 (b + 38) == 0) (b + 40) (toFloat b + 41.5 - 1) ((if b == 1 then 'q' else '?')) ((if b == 1 then "s43" else "?")) (modBy 2 (b + 43) == 0) (b + 45) (toFloat b + 46.5 - 1) ((if b == 1 then 'v' else '?')) ((if b == 1 then "s48" else "?")) (modBy 2 (b + 48) == 0) (b + 50) (toFloat b + 51.5 - 1) ((if b == 1 then 'a' else '?')) ((if b == 1 then "s53" else "?")) (modBy 2 (b + 53) == 0) (b + 55) (toFloat b + 56.5 - 1) ((if b == 1 then 'f' else '?')) ((if b == 1 then "s58" else "?")) (modBy 2 (b + 58) == 0) (b + 60) (toFloat b + 61.5 - 1) ((if b == 1 then 'k' else '?')) ((if b == 1 then "s63" else "?")) (modBy 2 (b + 63) == 0) (b + 65) (toFloat b + 66.5 - 1) ((if b == 1 then 'p' else '?')) ((if b == 1 then "s68" else "?")) (modBy 2 (b + 68) == 0) (b + 70) (toFloat b + 71.5 - 1) ((if b == 1 then 'u' else '?')) ((if b == 1 then "s73" else "?")) (modBy 2 (b + 73) == 0) (b + 75) (toFloat b + 76.5 - 1) ((if b == 1 then 'z' else '?')) ((if b == 1 then "s78" else "?")) (modBy 2 (b + 78) == 0) (b + 80) (toFloat b + 81.5 - 1) ((if b == 1 then 'e' else '?')) ((if b == 1 then "s83" else "?")) (modBy 2 (b + 83) == 0) (b + 85) (toFloat b + 86.5 - 1) ((if b == 1 then 'j' else '?')) ((if b == 1 then "s88" else "?")) (modBy 2 (b + 88) == 0) (b + 90)

step4 h b =
    h (toFloat b + 91.5 - 1) ((if b == 1 then 'o' else '?')) ((if b == 1 then "s93" else "?")) (modBy 2 (b + 93) == 0) (b + 95) (toFloat b + 96.5 - 1) ((if b == 1 then 't' else '?')) ((if b == 1 then "s98" else "?")) (modBy 2 (b + 98) == 0) (b + 100) (toFloat b + 101.5 - 1) ((if b == 1 then 'y' else '?')) ((if b == 1 then "s103" else "?")) (modBy 2 (b + 103) == 0) (b + 105) (toFloat b + 106.5 - 1) ((if b == 1 then 'd' else '?')) ((if b == 1 then "s108" else "?")) (modBy 2 (b + 108) == 0) (b + 110) (toFloat b + 111.5 - 1) ((if b == 1 then 'i' else '?')) ((if b == 1 then "s113" else "?")) (modBy 2 (b + 113) == 0) (b + 115) (toFloat b + 116.5 - 1) ((if b == 1 then 'n' else '?')) ((if b == 1 then "s118" else "?")) (modBy 2 (b + 118) == 0) (b + 120) (toFloat b + 121.5 - 1) ((if b == 1 then 's' else '?')) ((if b == 1 then "s123" else "?")) (modBy 2 (b + 123) == 0) (b + 125) (toFloat b + 126.5 - 1) ((if b == 1 then 'x' else '?')) ((if b == 1 then "s128" else "?")) (modBy 2 (b + 128) == 0) (b + 130) (toFloat b + 131.5 - 1) ((if b == 1 then 'c' else '?')) ((if b == 1 then "s133" else "?")) (modBy 2 (b + 133) == 0) (b + 135) (toFloat b + 136.5 - 1) ((if b == 1 then 'h' else '?')) ((if b == 1 then "s138" else "?")) (modBy 2 (b + 138) == 0) (b + 140) (toFloat b + 141.5 - 1) ((if b == 1 then 'm' else '?')) ((if b == 1 then "s143" else "?")) (modBy 2 (b + 143) == 0) (b + 145) (toFloat b + 146.5 - 1) ((if b == 1 then 'r' else '?')) ((if b == 1 then "s148" else "?")) (modBy 2 (b + 148) == 0) (b + 150) (toFloat b + 151.5 - 1) ((if b == 1 then 'w' else '?')) ((if b == 1 then "s153" else "?")) (modBy 2 (b + 153) == 0)

step5 h b =
    h (b + 155) (toFloat b + 156.5 - 1) ((if b == 1 then 'b' else '?')) ((if b == 1 then "s158" else "?")) (modBy 2 (b + 158) == 0) (b + 160) (toFloat b + 161.5 - 1) ((if b == 1 then 'g' else '?')) ((if b == 1 then "s163" else "?")) (modBy 2 (b + 163) == 0) (b + 165) (toFloat b + 166.5 - 1) ((if b == 1 then 'l' else '?')) ((if b == 1 then "s168" else "?")) (modBy 2 (b + 168) == 0) (b + 170) (toFloat b + 171.5 - 1) ((if b == 1 then 'q' else '?')) ((if b == 1 then "s173" else "?")) (modBy 2 (b + 173) == 0) (b + 175) (toFloat b + 176.5 - 1) ((if b == 1 then 'v' else '?')) ((if b == 1 then "s178" else "?")) (modBy 2 (b + 178) == 0) (b + 180) (toFloat b + 181.5 - 1) ((if b == 1 then 'a' else '?')) ((if b == 1 then "s183" else "?")) (modBy 2 (b + 183) == 0) (b + 185) (toFloat b + 186.5 - 1) ((if b == 1 then 'f' else '?')) ((if b == 1 then "s188" else "?")) (modBy 2 (b + 188) == 0) (b + 190) (toFloat b + 191.5 - 1) ((if b == 1 then 'k' else '?')) ((if b == 1 then "s193" else "?")) (modBy 2 (b + 193) == 0) (b + 195) (toFloat b + 196.5 - 1) ((if b == 1 then 'p' else '?')) ((if b == 1 then "s198" else "?")) (modBy 2 (b + 198) == 0) (b + 200) (toFloat b + 201.5 - 1) ((if b == 1 then 'u' else '?')) ((if b == 1 then "s203" else "?")) (modBy 2 (b + 203) == 0) (b + 205) (toFloat b + 206.5 - 1) ((if b == 1 then 'z' else '?')) ((if b == 1 then "s208" else "?")) (modBy 2 (b + 208) == 0) (b + 210) (toFloat b + 211.5 - 1) ((if b == 1 then 'e' else '?')) ((if b == 1 then "s213" else "?")) (modBy 2 (b + 213) == 0) (b + 215) (toFloat b + 216.5 - 1) ((if b == 1 then 'j' else '?')) ((if b == 1 then "s218" else "?")) (modBy 2 (b + 218) == 0)

step6 h b =
    h (b + 220) (toFloat b + 221.5 - 1) ((if b == 1 then 'o' else '?')) ((if b == 1 then "s223" else "?")) (modBy 2 (b + 223) == 0) (b + 225) (toFloat b + 226.5 - 1) ((if b == 1 then 't' else '?')) ((if b == 1 then "s228" else "?")) (modBy 2 (b + 228) == 0) (b + 230) (toFloat b + 231.5 - 1) ((if b == 1 then 'y' else '?')) ((if b == 1 then "s233" else "?")) (modBy 2 (b + 233) == 0) (b + 235) (toFloat b + 236.5 - 1) ((if b == 1 then 'd' else '?')) ((if b == 1 then "s238" else "?")) (modBy 2 (b + 238) == 0) (b + 240) (toFloat b + 241.5 - 1) ((if b == 1 then 'i' else '?')) ((if b == 1 then "s243" else "?")) (modBy 2 (b + 243) == 0) (b + 245) (toFloat b + 246.5 - 1) ((if b == 1 then 'n' else '?')) ((if b == 1 then "s248" else "?")) (modBy 2 (b + 248) == 0) (b + 250) (toFloat b + 251.5 - 1) ((if b == 1 then 's' else '?')) ((if b == 1 then "s253" else "?")) (modBy 2 (b + 253) == 0) (b + 255) (toFloat b + 256.5 - 1) ((if b == 1 then 'x' else '?')) ((if b == 1 then "s258" else "?")) (modBy 2 (b + 258) == 0) (b + 260) (toFloat b + 261.5 - 1) ((if b == 1 then 'c' else '?')) ((if b == 1 then "s263" else "?")) (modBy 2 (b + 263) == 0) (b + 265) (toFloat b + 266.5 - 1) ((if b == 1 then 'h' else '?')) ((if b == 1 then "s268" else "?")) (modBy 2 (b + 268) == 0) (b + 270) (toFloat b + 271.5 - 1) ((if b == 1 then 'm' else '?')) ((if b == 1 then "s273" else "?")) (modBy 2 (b + 273) == 0) (b + 275) (toFloat b + 276.5 - 1) ((if b == 1 then 'r' else '?')) ((if b == 1 then "s278" else "?")) (modBy 2 (b + 278) == 0) (b + 280) (toFloat b + 281.5 - 1) ((if b == 1 then 'w' else '?')) ((if b == 1 then "s283" else "?")) (modBy 2 (b + 283) == 0) (b + 285) (toFloat b + 286.5 - 1) ((if b == 1 then 'b' else '?')) ((if b == 1 then "s288" else "?")) (modBy 2 (b + 288) == 0) (b + 290) (toFloat b + 291.5 - 1) ((if b == 1 then 'g' else '?')) ((if b == 1 then "s293" else "?")) (modBy 2 (b + 293) == 0) (b + 295) (toFloat b + 296.5 - 1) ((if b == 1 then 'l' else '?')) ((if b == 1 then "s298" else "?")) (modBy 2 (b + 298) == 0)


map : (a -> b) -> List a -> List b
map f xs =
    case xs of
        [] ->
            []

        x :: rest ->
            f x :: map f rest


main =
    let
        base =
            1 + (Char.toCode 'b' - Char.toCode 'a') - 1

        fs0 =
            [ big ]

        fs1 =
            map (\h -> step0 h base) fs0

        fs2 =
            map (\h -> step1 h base) fs1

        fs3 =
            map (\h -> step2 h base) fs2

        fs4 =
            map (\h -> step3 h base) fs3

        fs5 =
            map (\h -> step4 h base) fs4

        fs6 =
            map (\h -> step5 h base) fs5

        fs7 =
            map (\h -> step6 h base) fs6

        _ =
            Debug.log "res" (fs7)

    in
    text "done"
