# md2txt.awk：把 spec/lark-spec.*.md 转成 RFC 风格的纯文本（RFC 7322）：每行最多 72 列，正文缩进 3 格，
# 每页 56 行加换页符，页眉页脚，目录带页码。中文按显示宽度折行（一个汉字算 2 列）。
# 只认 spec 用到的 Markdown：# 标题、## / ### 小节、段落（一行一段）、- 列表、1. 列表、``` 代码块、表格、
# `代码`、**粗体**、[文字](链接)，以及开头的 <!-- txt … --> 注释（首页和页眉页脚的文字）。
# 用法（在仓库根目录）：
#   LC_ALL=C awk -v lang=en -f spec/md2txt.awk spec/lark-spec.en.md > spec/lark-spec.en.txt
#   LC_ALL=C awk -v lang=zh -f spec/md2txt.awk spec/lark-spec.zh.md > spec/lark-spec.zh.txt
# 必须用 LC_ALL=C：脚本按字节处理 UTF-8。

BEGIN {
    for (i = 1; i < 256; i++) ORD[sprintf("%c", i)] = i
    W = 72
    CLOSE = "，。、；：）」』！？》”"
    OPEN = "（「『《“"
}

{ M[++NM] = $0 }

END { main() }

# ---------- 宽度和折行 ----------

function width(s,   i, n, b, w) {
    n = length(s); w = 0
    for (i = 1; i <= n; i++) {
        b = ORD[substr(s, i, 1)]
        if (b < 128) w++
        else if (b >= 240) { w += 2; i += 3 }
        else if (b >= 224) { w += 2; i += 2 }
        else if (b >= 192) { w += 1; i += 1 }
    }
    return w
}

function spaces(n,   s) { s = ""; while (n-- > 0) s = s " "; return s }

function rep(c, n,   s) { s = ""; while (n-- > 0) s = s c; return s }

# 切成 TK[1..k]：空格 "s"、连续的 ASCII "a"、一个多字节字符 "m"
function tokens(s,   i, j, n, b, c, k, l) {
    n = length(s); k = 0; i = 1
    while (i <= n) {
        c = substr(s, i, 1); b = ORD[c]
        if (c == " ") { TK[++k] = " "; TT[k] = "s"; i++; continue }
        if (b < 128) {
            j = i
            while (j <= n && substr(s, j, 1) != " " && ORD[substr(s, j, 1)] < 128) j++
            TK[++k] = substr(s, i, j - i); TT[k] = "a"; i = j; continue
        }
        l = (b >= 240) ? 4 : (b >= 224) ? 3 : (b >= 192) ? 2 : 1
        TK[++k] = substr(s, i, l); TT[k] = "m"; i += l
    }
    return k
}

# 折行：结果在 WL[1..n]。p1 是第一行的前缀，p2 是后面各行的前缀，每行最多 maxw 列
function wrap(s, p1, p2, maxw,   k, i, g, sp, glue, j, line, lw, has, add, n) {
    k = tokens(s); g = 0; sp = 0; LASTTK = ""; LASTTT = ""
    for (i = 1; i <= k; i++) {
        if (TT[i] == "s") { sp = 1; continue }
        glue = 0
        if (g > 0 && !sp) {
            if (index(CLOSE, TK[i]) || index(OPEN, LASTTK)) glue = 1
            if (TT[i] == "a" && TK[i] ~ /^[,.;:)\]!?]/) glue = 1
            if (LASTTT == "a" && LASTTK ~ /[(\[]$/) glue = 1
        }
        if (glue) G[g] = G[g] TK[i]
        else { G[++g] = TK[i]; GSP[g] = sp }
        LASTTK = TK[i]; LASTTT = TT[i]; sp = 0
    }
    n = 0; line = p1; lw = width(p1); has = 0
    for (j = 1; j <= g; j++) {
        add = (has && GSP[j]) ? " " G[j] : G[j]
        if (has && lw + width(add) > maxw) {
            WL[++n] = line; line = p2 G[j]; lw = width(line); continue
        }
        line = line add; lw += width(add); has = 1
    }
    WL[++n] = line
    for (j = 1; j <= n; j++) gsub(/\004/, " ", WL[j])
    return n
}

# 一组词里最长的不能断开的一段（表格的列不能比它窄）
function longest(s,   n, i, m, w) {
    n = wrap(s, "", "", 1); m = 0
    for (i = 1; i <= n; i++) { w = width(WL[i]); if (w > m) m = w }
    return m
}

# ---------- 行内的标记 ----------

function code(c) {
    if (length(c) <= 24) gsub(/ /, "\004", c)    # 短的代码片段不折开
    if (lang == "zh") return c
    if (index(c, "\"")) return "'" c "'"
    return "\"" c "\""
}

function plain(s,   p, q, r, t) {
    gsub(/\*\*/, "", s)
    for (;;) {
        p = index(s, "](")
        if (p == 0) break
        q = p
        while (q > 0 && substr(s, q, 1) != "[") q--
        r = index(substr(s, p), ")")
        if (q == 0 || r == 0) break
        t = substr(s, q + 1, p - q - 1)
        s = substr(s, 1, q - 1) t substr(s, p + r)
    }
    return s
}

function inl(s,   n, i, out) {
    n = split(s, P, "`"); out = ""
    for (i = 1; i <= n; i++) out = out ((i % 2) ? plain(P[i]) : code(P[i]))
    gsub(/\001/, "|", out)
    return out
}

# ---------- 收集要输出的行 ----------
# RT[i] 文字，RK[i] 种类（text / blank / head / toc），RG[i] 所在的组；GS[g] 组的行数，GK[g] 组的种类（keep / para / head）

function emit(t, k) { RT[++NR_] = t; RK[NR_] = k; RG[NR_] = NG; GS[NG]++ }

function group(kind) { NG++; GS[NG] = 0; GK[NG] = kind }

function blank() { if (NR_ > 0 && RK[NR_] != "blank") { RT[++NR_] = ""; RK[NR_] = "blank"; RG[NR_] = 0 } }

function para(s, p1, p2,   n, i) {
    group("para")
    n = wrap(inl(s), p1, p2, W)
    for (i = 1; i <= n; i++) emit(WL[i], "text")
    blank()
}

function headtext(s) {
    sub(/^#+ /, "", s)
    if (s ~ /^[0-9][0-9.]*\. / || s ~ /^Appendix [A-Z]\. / || s ~ /^附录 [A-Z]\. /) sub(/\. /, ".  ", s)
    return plain(s)
}

function table(a, b,   r, c, n, nc, cell, i, j, k, sum, avail, mx, wi, line, h, border, hb, nl) {
    nc = 0; n = 0
    for (r = a; r <= b; r++) {
        line = M[r]
        if (line ~ /^\|[-| ]+\|$/) continue
        gsub(/\\\|/, "\001", line)
        sub(/^\| */, "", line); sub(/ *\|$/, "", line)
        k = split(line, cell, / *\| */)
        n++
        for (c = 1; c <= k; c++) TC[n, c] = inl(cell[c])
        if (k > nc) nc = k
    }
    for (c = 1; c <= nc; c++) { NW[c] = 0; MW[c] = 0 }
    for (i = 1; i <= n; i++) for (c = 1; c <= nc; c++) {
        wi = width(TC[i, c]); if (wi > NW[c]) NW[c] = wi
        wi = longest(TC[i, c]); if (wi > MW[c]) MW[c] = wi
    }
    avail = W - 3 - (nc + 1) - 2 * nc
    for (;;) {
        sum = 0; mx = 0
        for (c = 1; c <= nc; c++) { sum += NW[c]; if (NW[c] > MW[c] && (mx == 0 || NW[c] > NW[mx])) mx = c }
        if (sum <= avail || mx == 0) break
        NW[mx]--
    }
    border = "   +"; hb = "   +"
    for (c = 1; c <= nc; c++) { border = border rep("-", NW[c] + 2) "+"; hb = hb rep("=", NW[c] + 2) "+" }
    group("keep")
    emit(border, "text")
    for (i = 1; i <= n; i++) {
        h = 1
        for (c = 1; c <= nc; c++) {
            CN[c] = wrap(TC[i, c], "", "", NW[c])
            for (j = 1; j <= CN[c]; j++) CL[c, j] = WL[j]
            if (CN[c] > h) h = CN[c]
        }
        for (j = 1; j <= h; j++) {
            line = "   |"
            for (c = 1; c <= nc; c++) {
                t = (j <= CN[c]) ? CL[c, j] : ""
                line = line " " t spaces(NW[c] - width(t)) " |"
            }
            emit(line, "text")
        }
        emit(i == 1 ? hb : border, "text")
    }
    blank()
}

function three(l, c, r,   lw, cw, rw, cs) {
    lw = width(l); cw = width(c); rw = width(r)
    cs = int((W - cw) / 2)
    if (cs < lw + 1) cs = lw + 1
    return l spaces(cs - lw) c spaces(W - rw - cs - cw) r
}

function main(   i, j, s, nh, intoc, incode, n, t, a, b, nl, nr, lines, toc_title, nm) {
    # 开头的注释：首页左右两栏、页眉、页脚
    nl = 0; nr = 0
    for (i = 1; i <= NM; i++) {
        if (M[i] == "<!-- txt") { incode = 1; continue }
        if (incode && M[i] == "-->") { incode = 0; continue }
        if (!incode) continue
        if (M[i] ~ /^left: /) { LEFT[++nl] = substr(M[i], 7) }
        else if (M[i] ~ /^right: /) { RIGHT[++nr] = substr(M[i], 8) }
        else if (M[i] ~ /^running: /) split(substr(M[i], 10), RUN, "|")
        else if (M[i] ~ /^footer: /) split(substr(M[i], 9), FOOT, "|")
    }
    toc_title = (lang == "zh") ? "目录" : "Table of Contents"
    # 目录里列出目录之后的 ## 和 ### 标题
    nh = 0; t = 0
    for (i = 1; i <= NM; i++) {
        if (M[i] == "```") incode = !incode
        if (incode) continue
        if (M[i] == "## " toc_title) { t = 1; continue }
        if (t && M[i] ~ /^###? /) { HT[++nh] = headtext(M[i]); HL[nh] = (M[i] ~ /^### /) ? 3 : 2 }
    }
    # 首页
    group("keep")
    lines = (nl > nr) ? nl : nr
    for (i = 1; i <= lines; i++) {
        a = (i <= nl) ? LEFT[i] : ""; b = (i <= nr) ? RIGHT[i] : ""
        emit(a spaces(W - width(a) - width(b)) b, "text")
    }
    emit("", "text"); emit("", "text")
    nm = 0; incode = 0; intoc = 0; t = 0
    for (i = 1; i <= NM; i++) {
        s = M[i]
        if (s == "<!-- txt") { incode = 2; continue }
        if (incode == 2) { if (s == "-->") incode = 0; continue }
        if (s == "```") {
            if (incode) { incode = 0; blank() } else { incode = 1; group("keep") }
            continue
        }
        if (incode) { emit(s == "" ? "" : "      " s, "text"); continue }
        if (s ~ /^# /) {
            group("keep"); n = wrap(plain(substr(s, 3)), "", "", W - 10)
            for (j = 1; j <= n; j++) emit(spaces(int((W - width(WL[j])) / 2)) WL[j], "text")
            blank(); continue
        }
        if (s ~ /^###? /) {
            intoc = (s == "## " toc_title); if (intoc) seen = 1
            blank(); group("head")
            if (intoc) {
                emit(toc_title, "head"); blank()
                group("para")
                for (j = 1; j <= nh; j++) { RH[NR_ + 1] = j; emit("", "toc") }
                blank()
            } else {
                if (seen) RH[NR_ + 1] = ++t
                emit(headtext(s), "head"); blank()
            }
            continue
        }
        if (intoc || s == "") continue
        if (s ~ /^\|/) {
            a = i
            while (i + 1 <= NM && M[i + 1] ~ /^\|/) i++
            table(a, i); continue
        }
        if (s ~ /^- /) { para(substr(s, 3), "   o  ", "      "); continue }
        if (s ~ /^  - /) { para(substr(s, 5), "      +  ", "         "); continue }
        if (s ~ /^[0-9]+\. /) {
            n = index(s, ". ")
            para(substr(s, n + 2), "   " substr(s, 1, n) "  ", "       "); continue
        }
        para(s, "   ", "   ")
    }
    paginate()
}

# ---------- 分页 ----------

function paginate(   i, pg, pos, cap, need, g, h, k, line, num, w, out, lab) {
    pg = 1; pos = 0; cap = 53
    for (i = 1; i <= NR_; i++) {
        if (RK[i] == "blank" && pos == 0) { PG[i] = 0; continue }
        g = RG[i]
        if (g > 0 && (i == 1 || RG[i - 1] != g)) {
            if (GK[g] == "head") need = 5
            else if (GK[g] == "keep") need = (GS[g] <= 50) ? GS[g] : 2
            else need = (GS[g] >= 2) ? 2 : 1
            if (pos > 0 && pos + need > cap) { pg++; pos = 0; cap = 50 }
        }
        if (pos >= cap) {
            if (RK[i] == "blank") { PG[i] = 0; continue }
            pg++; pos = 0; cap = 50
        }
        PG[i] = pg; pos++
        if (RK[i] == "head" && RH[i] > 0) HP[RH[i]] = pg
    }
    NP = pg
    # 目录的行
    for (i = 1; i <= NR_; i++) {
        if (RK[i] != "toc") continue
        h = RH[i]
        line = ((HL[h] == 3) ? "     " : "   ") HT[h] " "
        w = width(line)
        if (w % 2 == 1) { line = line " "; w++ }
        while (w <= 66) { line = line ". "; w += 2 }
        num = HP[h] ""
        RT[i] = line spaces(W - w - length(num)) num
    }
    # 输出
    pg = 0
    for (i = 1; i <= NR_; i++) {
        if (PG[i] == 0) continue
        if (PG[i] != pg) {
            if (pg > 0) footer(pg, pos)
            pg = PG[i]; pos = 0
            if (pg > 1) { print three(RUN[1], RUN[2], RUN[3]); print ""; print ""; }
        }
        sub(/ +$/, "", RT[i])
        print RT[i]; pos++
    }
    footer(pg, pos)
}

function footer(pg, pos,   cap, lab) {
    cap = (pg == 1) ? 53 : 50
    while (pos < cap) { print ""; pos++ }
    lab = (lang == "zh") ? "[第 " pg " 页]" : "[Page " pg "]"
    print ""; print ""
    print three(FOOT[1], FOOT[2], lab)
    if (pg < NP) printf "\f\n"
}
