# -*- coding: utf-8 -*-
import tkinter as tk
import hashlib, hmac as _hmac, math, random, re

# ============== 密码学核心（步骤格式与课程 PS1 标准答案一致）==============
def _exp_decomp(e):
    """1137 -> '1137 = 1024+64+32+16+1'"""
    parts = [str(1 << i) for i in range(e.bit_length() - 1, -1, -1) if (e >> i) & 1]
    return f'{e} = ' + '+'.join(parts)

def _pow_trace(b, e, m):
    """课程风格幂运算链：指数≤8 逐次乘；>8 二进制分解平方。返回 (结果, [行])"""
    b, e, m = int(b), int(e), int(m)
    bm = b % m
    if e == 0: return 1 % m, [f'{b}^0 = 1']
    if e == 1:
        return bm, [f'{b}^1 = {bm}' + (f' mod {m} = {bm}' if b >= m else '')]
    if e <= 8:
        lines, v = [], bm
        lines.append(f'{b}^1 = {bm}' + (f' mod {m} = {bm}' if b >= m else ''))
        for i in range(2, e + 1):
            raw = v * bm; nv = raw % m
            lines.append(f'{b}^{i} = {b}×{v} = {raw} mod {m} = {nv}')
            v = nv
        return v, lines
    # 二进制分解：b^(2^k) 链 + 按需相乘（课程 Q3a/Q4 风格）
    lines = [_exp_decomp(e)]
    max_k = e.bit_length() - 1
    powers = [bm]
    if max_k >= 1:
        raw = bm * bm; v = raw % m
        lines.append(f'{b}^2 = {bm}² = {raw} mod {m} = {v}')
        powers.append(v)
    for k in range(2, max_k + 1):
        raw = powers[-1] * powers[-1]; v = raw % m
        lines.append(f'{b}^{2**k} = ({powers[-2]})² = {raw} mod {m} = {v}')
        powers.append(v)
    need = [k for k in range(max_k + 1) if (e >> k) & 1]
    if len(need) == 1:
        result = powers[need[0]]
    else:
        acc = powers[need[0]]; expr = f'{b}^{e} = {b}^{2**need[0]}'
        for k in need[1:]:
            raw = acc * powers[k]; nv = raw % m
            expr += f'×{b}^{2**k}'
            lines.append(f'{expr} = {acc}×{powers[k]} = {raw} mod {m} = {nv}')
            acc = nv; expr = f'      '
        result = acc
    return result, lines

def powmod_fn(base, exp, mod):
    """课程 Q3a 风格：二进制分解 + MSB→LSB 逐位表"""
    base, exp, mod = int(base), int(exp), int(mod)
    if mod == 1: return 0, f'{base}^{exp} mod 1 = 0'
    bits = bin(exp)[2:]
    steps = [f'{base}^{exp} mod {mod}:', f'  {_exp_decomp(exp)}',
             f'  {exp} = {bits}₂（{len(bits)} 位）',
             f'  从 result=1 开始，MSB→LSB 逐位：']
    result, bm = 1, base % mod
    for i, bit in enumerate(bits, 1):
        sq_raw = result * result; sq = sq_raw % mod
        sq_txt = f'{result}² = {sq_raw} mod {mod} = {sq}'
        if bit == '1':
            m_raw = sq * bm; m_res = m_raw % mod
            steps.append(f'  Step {i:2d} bit=1: {sq_txt}，×{bm} = {m_raw} mod {mod} = {m_res} → {m_res}')
            result = m_res
        else:
            steps.append(f'  Step {i:2d} bit=0: {sq_txt} → {sq}')
            result = sq
    steps.append(f'  {base}^{exp} mod {mod} = {result}')
    return result, '\n'.join(steps)

def gcd_fn(a, b):
    """课程 Q3c 风格：大数在前，'a = q×b + r'，编号步骤，最后一个非零余数"""
    a, b = abs(int(a)), abs(int(b))
    if a < b: a, b = b, a
    oa, ob = a, b
    steps = [f'gcd({oa},{ob}):', f'  欧几里得算法：']
    i = 1
    while b:
        q, r = divmod(a, b)
        steps.append(f'  Step {i:2d}: {a} = {q}×{b} + {r}')
        a, b = b, r; i += 1
    steps.append(f'  最后一个非零余数 = {a}')
    steps.append(f'  gcd({oa},{ob}) = {a}')
    return a, '\n'.join(steps)

def modinv_fn(a, m):
    """课程 Q3d/Q3e 风格：正向欧几里得 + 回代 + 验证"""
    a0, m0 = int(a), int(m)
    big, small = max(abs(a0), abs(m0)), min(abs(a0), abs(m0))
    # 正向
    A, B = big, small
    divs = []  # (A_i, B_i, q_i, R_i)
    while B:
        q, R = divmod(A, B)
        divs.append((A, B, q, R))
        A, B = B, R
    g = A
    steps = [f'modinv({a0},{m0}):', f'  正向欧几里得：']
    for i, (Ai, Bi, qi, Ri) in enumerate(divs, 1):
        steps.append(f'  Step {i:2d}: {Ai} = {qi}×{Bi} + {Ri}')
    steps.append(f'  gcd = {g}')
    if g != 1:
        steps.append(f'  ✗ gcd={g}≠1，{a0} 与 {m0} 不互素，逆元不存在')
        return None, '\n'.join(steps)
    # 回代：gcd = ca*A_i + cb*B_i，从最后一个非零余数往前
    n = len(divs)
    if n == 1:
        ca, cb = 0, 1  # gcd = small = 1
    else:
        Ai, Bi, qi, Ri = divs[n - 2]  # gcd = R_i = A_i − q_i×B_i
        ca, cb = 1, -qi
        steps.append(f'  回代（back-substitution）：')
        steps.append(f'  {g} = {Ai} − {qi}×{Bi}')
        for i in range(n - 3, -1, -1):
            # 当前 g = ca×A_{i+1} + cb×B_{i+1}，其中 A_{i+1}=B_i, B_{i+1}=R_i=A_i−q_i×B_i
            Ai2, Bi2, qi2, Ri2 = divs[i]
            # g = ca×B_i + cb×(A_i − q_i×B_i) = cb×A_i + (ca − cb×q_i)×B_i
            nca, ncb = cb, ca - cb * qi2
            steps.append(f'    = {nca}×{Ai2} + ({ncb})×{Bi2}'
                         .replace('+ (-', '− (').replace(')×', ')×'))
            ca, cb = nca, ncb
    # 最终 g = ca×big + cb×small；a0 的系数即逆元候选
    coef_a = ca if abs(a0) == big else cb
    if a0 < 0: coef_a = -coef_a
    inv = coef_a % m0
    steps.append(f'  {g} = {ca}×{big} + ({cb})×{small}')
    steps.append(f'  {a0}⁻¹ mod {m0} = {inv}')
    prod = a0 * inv
    steps.append(f'  验证: {a0}×{inv} = {prod}')
    steps.append(f'  {prod} mod {m0} = {prod % m0} ✓')
    return inv, '\n'.join(steps)

def euler_phi(n):
    """课程 Q3b 风格：除法链分解 + 大因子素性验证 + φ 公式"""
    n0 = int(n)
    if n0 < 1: return 0, 'phi: n 必须 ≥ 1'
    if n0 == 1: return 1, 'phi(1) = 1'
    steps = [f'phi({n0}):', f'  先分解 {n0}：']
    factors = {}; n = n0; d = 2
    while d * d <= n:
        while n % d == 0:
            steps.append(f'  {n} ÷ {d} = {n // d}')
            factors[d] = factors.get(d, 0) + 1; n //= d
        d += 1
    if n > 1: factors[n] = factors.get(n, 0) + 1
    # 分解式
    ftxt = '×'.join(f'{p}' + (f'^{k}' if k > 1 else '') for p, k in sorted(factors.items()))
    steps.append(f'  {n0} = {ftxt}')
    # 大因子素性说明（课程对 379 的写法）
    for p in sorted(factors):
        if p > 40:
            lim = math.isqrt(p)
            primes_up = [x for x in [2,3,5,7,11,13,17,19,23,29,31,37] if x <= lim]
            steps.append(f'  √{p}≈{math.sqrt(p):.1f}，{p} 不被 {"、".join(map(str, primes_up))} 整除 → {p} 是素数')
    ps = sorted(factors)
    if len(ps) == 2 and all(factors[p] == 1 for p in ps):
        p, q = ps
        result = (p - 1) * (q - 1)
        steps.append(f'  φ({n0}) = φ({p})×φ({q}) = ({p}−1)×({q}−1) = {p-1}×{q-1} = {result}')
    elif len(ps) == 1:
        p, k = ps[0], factors[ps[0]]
        result = n0 - n0 // p
        if k == 1:
            steps.append(f'  {n0} 是素数 → φ({n0}) = {n0}−1 = {result}')
        else:
            steps.append(f'  φ({p}^{k}) = {p}^{k} − {p}^{k-1} = {n0} − {n0//p} = {result}')
    else:
        prod_txt = '×'.join(f'(1−1/{p})' for p in ps)
        result = n0
        for p in ps: result = result // p * (p - 1)
        steps.append(f'  φ({n0}) = {n0}×{prod_txt} = {result}')
    return result, '\n'.join(steps)

def is_prime(n):
    """课程 Q3f 风格：试除所有 ≤√n 的素数，确定性输出"""
    n = int(n); steps = [f'isprime({n}):']
    if n < 2:
        steps.append('  n < 2 → 合数'); return False, '\n'.join(steps)
    small = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]
    for p in small:
        if n == p:
            steps.append(f'  {n} 是素数'); return True, '\n'.join(steps)
        if n % p == 0:
            steps.append(f'  {n} = {p} × {n//p} → 合数'); return False, '\n'.join(steps)
    if n < 41 * 41:
        steps.append(f'  n < 41²，已排除所有可能因子 → 素数'); return True, '\n'.join(steps)
    if n < 10**10:
        limit = math.isqrt(n)
        steps.append(f'  √n ≈ {math.sqrt(n):.1f}，试除所有 ≤{limit} 的素数...')
        for i in range(41, limit + 1, 2):
            if n % i == 0:
                steps.append(f'  {n} = {i} × {n//i} → 合数'); return False, '\n'.join(steps)
        steps.append(f'  所有 ≤√n 的素数均不整除 {n} → 素数')
        return True, '\n'.join(steps)
    r, d = 0, n - 1
    while d % 2 == 0: r += 1; d //= 2
    steps.append(f'  n 较大，用 Miller-Rabin：n−1 = 2^{r} × {d}')
    for a in small:
        x = pow(a, d, n)
        if x == 1 or x == n - 1:
            steps.append(f'  a={a}: {a}^{d} ≡ {x} (mod n) 通过'); continue
        passed = False
        for i in range(r - 1):
            x = pow(x, 2, n)
            if x == n - 1:
                steps.append(f'  a={a}: 连续平方后 ≡ −1 (mod n) 通过'); passed = True; break
        if not passed:
            steps.append(f'  a={a}: 见证 {n} 为合数 → 合数'); return False, '\n'.join(steps)
    steps.append('  全部基通过 → 素数'); return True, '\n'.join(steps)

def rsa_enc(m, e, n):
    m, e, n = int(m), int(e), int(n)
    c, trace = _pow_trace(m, e, n)
    steps = [f'RSA 加密: c = m^e mod n = {m}^{e} mod {n}'] + ['  ' + l for l in trace] + [f'c = {c}']
    return c, '\n'.join(steps)

def rsa_dec(c, d, n):
    c, d, n = int(c), int(d), int(n)
    m, trace = _pow_trace(c, d, n)
    steps = [f'RSA 解密: m = c^d mod n = {c}^{d} mod {n}'] + ['  ' + l for l in trace] + [f'm = {m}']
    return m, '\n'.join(steps)

def elgamal_enc(m, g, A, p, r):
    """课程 Q4b 风格"""
    m, g, A, p, r = int(m), int(g), int(A), int(p), int(r)
    c1, t1 = _pow_trace(g, r, p)
    s, t2 = _pow_trace(A, r, p)
    c2 = (m * s) % p
    steps = [f'ElGamal 加密 M={m}，随机数 r={r}：',
             f'  c1 = g^r mod p = {g}^{r} mod {p}'] + ['    ' + l for l in t1] + [
             f'  c1 = {c1}',
             f'  s = y^r mod p = {A}^{r} mod {p}'] + ['    ' + l for l in t2] + [
             f'  s = {s}',
             f'  c2 = M×s mod p = {m}×{s} mod {p} = {m*s}' + (f' mod {p} = {c2}' if m*s >= p else ''),
             f'  密文 (c1, c2) = ({c1}, {c2})']
    return f'({c1}, {c2})', '\n'.join(steps)

def elgamal_dec(c1, c2, x, p):
    """课程 Q4c 风格"""
    c1, c2, x, p = int(c1), int(c2), int(x), int(p)
    s, t1 = _pow_trace(c1, x, p)
    si = pow(s, -1, p)
    m = (c2 * si) % p
    steps = [f'ElGamal 解密 (c1,c2)=({c1},{c2})，私钥 x={x}：',
             f'  Step 1: s = c1^x mod p = {c1}^{x} mod {p}'] + ['    ' + l for l in t1] + [
             f'  s = {s}',
             f'  Step 2: s⁻¹ mod {p}：{s}×{si} = {s*si} ≡ 1 (mod {p}) → s⁻¹ = {si}',
             f'  Step 3: M = c2×s⁻¹ mod p = {c2}×{si} = {c2*si} mod {p} = {m}',
             f'  M = {m} ✓']
    return m, '\n'.join(steps)

def dh_key(g, p, a, b):
    """课程 Q5 风格：A、B、双方各算 K，验证一致"""
    g, p, a, b = int(g), int(p), int(a), int(b)
    A, t1 = _pow_trace(g, a, p)
    B, t2 = _pow_trace(g, b, p)
    K, t3 = _pow_trace(B, a, p)
    K2, t4 = _pow_trace(A, b, p)
    steps = [f'DH 密钥交换 g={g}, p={p}：',
             f'  Alice: A = g^x mod p = {g}^{a} mod {p}'] + ['    ' + l for l in t1] + [
             f'  A = {A}',
             f'  Bob: B = g^y mod p = {g}^{b} mod {p}'] + ['    ' + l for l in t2] + [
             f'  B = {B}',
             f'  Alice 算: K = B^x mod p = {B}^{a} mod {p}'] + ['    ' + l for l in t3] + [
             f'  K = {K}',
             f'  Bob 验证: K = A^y mod p = {A}^{b} mod {p}'] + ['    ' + l for l in t4] + [
             f'  K = {K2} ✓ 双方一致' if K == K2 else f'  ✗ 不一致！']
    return K, '\n'.join(steps)

# ============== GUI ==============
class SciCalc:
    def __init__(self, root):
        self.root = root
        root.title("Calculator")
        # 足够大的固定窗口，保证所有区域都能显示
        root.geometry("480x780")
        root.resizable(False, False)
        root.configure(bg="#1e1e1e")
        
        self.disp = tk.StringVar(value="0")
        self.err_msg = tk.StringVar(value="")
        self._expr = ""
        self._mode = None
        self._input_vars = {}
        self._rsa_op = None; self._eg_op = None; self._sha_text = None
        
        self._build_fixed_layout()
        self._bind_keys()
    
    def _build_fixed_layout(self):
        """所有区域都 pack 在固定位置，永远不 pack_forget"""
        # ---- 1. 显示屏 ----
        df = tk.Frame(self.root, bg="#202020", height=72)
        df.pack(fill='x', padx=6, pady=(6,2))
        df.pack_propagate(False)
        tk.Entry(df, textvariable=self.disp, font=("Consolas", 26),
                 bg="#202020", fg="white", readonlybackground="#202020",
                 bd=0, highlightthickness=0, justify='right',
                 state='readonly').pack(fill='x', expand=True, padx=10, pady=(8,0))
        tk.Label(df, textvariable=self.err_msg, font=("Arial",9),
                 bg="#202020", fg="#ff6666", anchor='e').pack(fill='x', padx=10, pady=(0,4))
        
        # ---- 2. ADV 槽位（永远占据固定高度，默认空白）----
        self.slot = tk.Frame(self.root, bg="#242424", height=210)
        self.slot.pack(fill='x', padx=6, pady=(2,0))
        self.slot.pack_propagate(False)
        self._slot_default = tk.Frame(self.slot, bg="#242424")
        self._slot_default.pack(fill='both', expand=True)
        
        # ---- 3. 科学函数（adv 混在第三排，与 sin/cos 同款样式，无差别伪装）----
        sci1 = tk.Frame(self.root, bg="#1e1e1e"); sci1.pack(fill='x', padx=6, pady=3)
        for t in ['sin','cos','tan','log','ln','√','π','x²']: self._sci_btn(sci1, t, "#4a4a4a")
        sci2 = tk.Frame(self.root, bg="#1e1e1e"); sci2.pack(fill='x', padx=6, pady=3)
        for t in ['sin⁻¹','cos⁻¹','tan⁻¹','10ˣ','eˣ','x³','MOD','±']: self._sci_btn(sci2, t, "#4a4a4a")
        # 第三排：混入 adv 功能，标签全部改成普通计算器风格小写
        sci3 = tk.Frame(self.root, bg="#1e1e1e"); sci3.pack(fill='x', padx=6, pady=3)
        self._adv_btn_refs = {}
        # (显示标签, 内部模式名) —— 标签看着像普通数学函数
        adv_items = [('powm','pow'),('inv','inv'),('gcd','gcd'),('φ','phi'),
                     ('prim','prime'),('rsa','RSA'),('elg','EG'),('dh','DH'),('mac','SHA')]
        for label, mode in adv_items:
            b = self._sci_btn(sci3, label, "#4a4a4a",
                              cmd=lambda m=mode: self._enter_mode(m))
            self._adv_btn_refs[mode] = b
        
        # ---- 5. 数字键盘 ----
        bf = tk.Frame(self.root, bg="#1e1e1e"); bf.pack(fill='both', expand=True, padx=6, pady=(3,6))
        std = [
            [("(","#4a4a4a"),(")","#4a4a4a"),("C","#5a4040"),("÷","#505050")],
            [("7","#3d3d3d"),("8","#3d3d3d"),("9","#3d3d3d"),("×","#505050")],
            [("4","#3d3d3d"),("5","#3d3d3d"),("6","#3d3d3d"),("−","#505050")],
            [("1","#3d3d3d"),("2","#3d3d3d"),("3","#3d3d3d"),("+","#505050")],
            [("0","#3d3d3d"),(".","#3d3d3d"),("exp","#4a4a4a"),("=","#506040")],
        ]
        for r, row in enumerate(std):
            for c, (t, col) in enumerate(row):
                self._mk_btn(bf, t, col, r, c, lambda x=t: self._on_std(x))
        for i in range(4): bf.columnconfigure(i, weight=1)
        for i in range(5): bf.rowconfigure(i, weight=1)
    
    def _sci_btn(self, p, t, col, cmd=None):
        b = tk.Button(p, text=t, font=("Arial",9,"bold"), bg=col, fg="#d0d0d0", bd=0, padx=8, pady=6,
                      activebackground="#5a5a5a", activeforeground="#ffffff",
                      command=cmd if cmd else (lambda x=t: self._on_sci(x)))
        b.pack(side='left', padx=2)
        return b
    
    def _mk_btn(self, p, t, col, r, ci, cmd):
        tk.Button(p, text=t, font=("Arial",15,"bold"), bg=col, fg="#e0e0e0", bd=0,
                  activebackground="#606060", activeforeground="#ffffff",
                  command=cmd).grid(row=r, column=ci, sticky='nsew', padx=2, pady=2)
    
    def _bind_keys(self):
        """不再做任何全局键盘拦截，输入框走系统原生输入，零干扰"""
        pass

    # === 普通计算 ===
    def _on_std(self, t):
        self.err_msg.set("")
        if t == "C": self._expr = ""; self.disp.set("0")
        elif t == "=": self._eval_expr()
        elif t == "exp": self._expr += "*10**"; self.disp.set(self._expr)
        elif t == "±":
            if self._expr.startswith("-"): self._expr = self._expr[1:]
            elif self._expr and self._expr != "0": self._expr = "-" + self._expr
            self.disp.set(self._expr)
        else:
            if self._expr == "0" and t not in ("+","−","×","÷","."): self._expr = ""
            self._expr += t; self.disp.set(self._expr)
    
    def _on_sci(self, t):
        self.err_msg.set("")
        if t == "MOD": self._expr += " % "; self.disp.set(self._expr); return
        try: v = float(self.disp.get())
        except: v = 0
        mp = {'sin':lambda:math.sin(math.radians(v)),'cos':lambda:math.cos(math.radians(v)),
              'tan':lambda:math.tan(math.radians(v)),'sin⁻¹':lambda:math.degrees(math.asin(max(-1,min(1,v)))),
              'cos⁻¹':lambda:math.degrees(math.acos(max(-1,min(1,v)))),'tan⁻¹':lambda:math.degrees(math.atan(v)),
              'log':lambda:math.log10(v) if v>0 else float('nan'),'ln':lambda:math.log(v) if v>0 else float('nan'),
              '√':lambda:math.sqrt(v) if v>=0 else float('nan'),
              'x²':lambda:v**2,'x³':lambda:v**3,'10ˣ':lambda:10**v,'eˣ':lambda:math.exp(v),
              'π':lambda:math.pi}
        if t in mp:
            r = mp[t]()
            if math.isnan(r): self.err_msg.set(f'{t} 定义域错误'); return
            self._expr = str(round(float(r), 10)); self.disp.set(self._expr)
    
    def _eval_expr(self):
        e = self._expr.replace("−","-").replace("×","*").replace("÷","/")
        e = e.replace("^", "**")  # 防止用户手输 ^ 被当成异或
        e = re.sub(r'\s*[Mm][Oo][Dd]\s*', ' % ', e)
        try:
            r = eval(e, {"__builtins__":{}})
            self._expr = str(round(float(r), 10)); self.disp.set(self._expr); self.err_msg.set("")
        except Exception as ex:
            self.err_msg.set(f'Err'); self.disp.set("Err")
    
    # === adv 模式：替换 slot 内容 ===
    def _enter_mode(self, mode):
        self._mode = mode; self.err_msg.set("")
        # 选中态与其他按钮差异极小：仅微亮，像普通按键被按下的样子
        for t, b in self._adv_btn_refs.items():
            b.config(bg="#565656" if t == mode else "#4a4a4a",
                     fg="#d0d0d0")
        # 清空 slot
        for w in self.slot.winfo_children(): w.destroy()
        self._input_vars = {}; self._sha_text = None
        
        self._build_slot_content(mode)

    def _mk_entry(self, parent, row, col, lbl, key):
        tk.Label(parent, text=lbl, font=("Arial",10,"bold"), bg="#242424", fg="#cccccc"
                 ).grid(row=row, column=col*2, padx=(8,3), pady=3, sticky='w')
        e = tk.Entry(parent, font=("Consolas",11), width=11, bg="#3a3a3a", fg="#ffffff",
                     insertbackground="#ffffff", relief='solid', bd=1,
                     highlightthickness=2, highlightbackground="#555555",
                     highlightcolor="#888888", selectbackground="#555555")
        e.grid(row=row, column=col*2+1, padx=3, pady=3, sticky='we')
        self._input_vars[key] = e
    
    def _build_slot_content(self, mode):
        # 输入区（slot 上半）
        inp = tk.Frame(self.slot, bg="#242424"); inp.pack(fill='x', pady=(4,0))
        
        if mode == "pow":
            self._mk_entry(inp, 0, 0, "base:", "base")
            self._mk_entry(inp, 0, 1, "exp:", "exp")
            self._mk_entry(inp, 0, 2, "mod:", "mod")
        elif mode == "inv":
            self._mk_entry(inp, 0, 0, "a:", "a")
            self._mk_entry(inp, 0, 1, "mod:", "m")
        elif mode == "gcd":
            self._mk_entry(inp, 0, 0, "a:", "a")
            self._mk_entry(inp, 0, 1, "b:", "b")
        elif mode == "phi":
            self._mk_entry(inp, 0, 0, "n:", "n")
        elif mode == "prime":
            self._mk_entry(inp, 0, 0, "n:", "n")
        elif mode == "RSA":
            self._rsa_op = tk.StringVar(value="enc")
            for i,(t,v) in enumerate([("enc","enc"),("dec","dec")]):
                tk.Radiobutton(inp, text=t, variable=self._rsa_op, value=v,
                               font=("Arial",9), bg="#242424", fg="#aaaaaa",
                               selectcolor="#242424", activebackground="#242424"
                              ).grid(row=0, column=i*2, padx=4, sticky='w')
            self._mk_entry(inp, 1, 0, "m/c:", "mc")
            self._mk_entry(inp, 1, 1, "e/d:", "ed")
            self._mk_entry(inp, 1, 2, "n:", "n")
        elif mode == "EG":
            self._eg_op = tk.StringVar(value="enc")
            for i,(t,v) in enumerate([("enc","enc"),("dec","dec")]):
                tk.Radiobutton(inp, text=t, variable=self._eg_op, value=v,
                               font=("Arial",9), bg="#242424", fg="#aaaaaa",
                               selectcolor="#242424", activebackground="#242424"
                              ).grid(row=0, column=i*2, padx=4, sticky='w')
            self._mk_entry(inp, 1, 0, "g:", "g"); self._mk_entry(inp, 1, 1, "p:", "p")
            self._mk_entry(inp, 1, 2, "A/x:", "k")
            self._mk_entry(inp, 2, 0, "m/c1:", "a"); self._mk_entry(inp, 2, 1, "r/c2:", "b")
        elif mode == "DH":
            self._mk_entry(inp, 0, 0, "g:", "g"); self._mk_entry(inp, 0, 1, "p:", "p")
            self._mk_entry(inp, 0, 2, "a:", "a"); self._mk_entry(inp, 0, 3, "b:", "b")
        elif mode == "SHA":
            tk.Label(inp, text="in:", font=("Arial",9), bg="#242424", fg="#999999"
                     ).grid(row=0, column=0, sticky='w', padx=4)
            self._sha_text = tk.Text(inp, height=1, font=("Consolas",9),
                                      bg="#151515", fg="#ffffff", relief='flat', bd=1,
                                      highlightthickness=1, highlightbackground="#3a3a3a")
            self._sha_text.grid(row=0, column=1, columnspan=6, sticky='we', padx=2)
            self._mk_entry(inp, 1, 0, "hkey:", "hkey")
        
        for c in range(8): inp.columnconfigure(c, weight=1)
        
        # 按钮行 + 结果（slot 下半）
        bottom = tk.Frame(self.slot, bg="#242424"); bottom.pack(fill='x', pady=(2,4))
        tk.Button(bottom, text="▶", bg="#3a3a3a", fg="#aaa", bd=0, padx=10, pady=2,
                  font=("Arial",9,"bold"), activebackground="#4a4a4a",
                  command=self._do_compute).pack(side='left', padx=2)
        tk.Button(bottom, text="📋复制", bg="#2a2a2a", fg="#888", bd=0, padx=8, pady=2,
                  font=("Arial",8), activebackground="#3a3a3a",
                  command=self._copy_result).pack(side='left', padx=2)
        tk.Button(bottom, text="✕", bg="#2a2a2a", fg="#888", bd=0, padx=8, pady=2,
                  font=("Arial",9), activebackground="#3a3a3a",
                  command=self._exit_mode).pack(side='right', padx=2)
        
        # 结果文本框（带滚动条，高度足够显示结论行）
        res_frame = tk.Frame(self.slot, bg="#242424")
        res_frame.pack(fill='both', expand=True, padx=4, pady=(0,4))
        sb = tk.Scrollbar(res_frame, orient='vertical')
        self.result_tb = tk.Text(res_frame, height=5, font=("Consolas",9),
                                  bg="#181818", fg="#cccccc", wrap='word',
                                  borderwidth=0, highlightthickness=0,
                                  yscrollcommand=sb.set)
        sb.config(command=self.result_tb.yview)
        sb.pack(side='right', fill='y')
        self.result_tb.pack(side='left', fill='both', expand=True)
        self.result_tb.config(state='disabled')
    
    def _exit_mode(self):
        self._mode = None
        for t, b in self._adv_btn_refs.items(): b.config(bg="#4a4a4a", fg="#d0d0d0")
        for w in self.slot.winfo_children(): w.destroy()
        tk.Frame(self.slot, bg="#242424").pack(fill='both', expand=True)
        self.err_msg.set("")
    
    def _parse(self, key):
        v = self._input_vars[key].get().strip().replace(',', '')
        if not v: raise ValueError(f'{key} 空')
        try: return int(v) if '.' not in v else float(v)
        except: raise ValueError(f'{key}="{v}" 无效')
    
    def _do_compute(self):
        m = self._mode; self.err_msg.set("")
        try:
            if m == "pow": r,s = powmod_fn(self._parse('base'), self._parse('exp'), self._parse('mod'))
            elif m == "inv":
                r,s = modinv_fn(self._parse('a'), self._parse('m'))
                if r is None: self.err_msg.set('无解'); self._set_result(s); return
            elif m == "gcd": r,s = gcd_fn(self._parse('a'), self._parse('b'))
            elif m == "phi": r,s = euler_phi(self._parse('n'))
            elif m == "prime":
                rr,s = is_prime(self._parse('n')); r = "✓" if rr else "✗"
            elif m == "RSA":
                fn = rsa_enc if self._rsa_op.get()=="enc" else rsa_dec
                r,s = fn(self._parse('mc'), self._parse('ed'), self._parse('n'))
            elif m == "EG":
                if self._eg_op.get()=="enc":
                    # elgamal_enc(m, g, A, p, r)：k 框=A, a 框=m, b 框=r
                    r,s = elgamal_enc(self._parse('a'), self._parse('g'),
                                      self._parse('k'), self._parse('p'), self._parse('b'))
                else:
                    # elgamal_dec(c1, c2, x, p)：k 框=x, a 框=c1, b 框=c2
                    r,s = elgamal_dec(self._parse('a'), self._parse('b'),
                                      self._parse('k'), self._parse('p'))
            elif m == "DH":
                r,s = dh_key(self._parse('g'), self._parse('p'),
                             self._parse('a'), self._parse('b'))
            elif m == "SHA":
                text = self._sha_text.get('1.0','end').strip().encode()
                if not text: self.err_msg.set('输入空'); return
                sha = hashlib.sha256(text).hexdigest()
                out = [sha]; k = self._input_vars['hkey'].get().strip()
                if k: out += [_hmac.new(k.encode(), text, hashlib.sha256).hexdigest()]
                r = sha[:14]+'...'; s = '\n'.join(out)
            else: return
            self.disp.set(str(r)); self._set_result(s)
        except ValueError as ex: self.err_msg.set(str(ex)); self._set_result(f'输入: {ex}')
        except Exception as ex: self.err_msg.set(f'错误'); self._set_result(f'{ex}')
    
    def _set_result(self, text):
        self.result_tb.config(state='normal'); self.result_tb.delete('1.0','end')
        self.result_tb.insert('1.0', text); self.result_tb.see('end')
        self.result_tb.config(state='disabled')
    
    def _copy_result(self):
        self.result_tb.config(state='normal')
        self.root.clipboard_clear(); self.root.clipboard_append(self.result_tb.get('1.0','end').strip())
        self.root.update(); self.result_tb.config(state='disabled'); self.err_msg.set('已复制')


def main():
    root = tk.Tk(); SciCalc(root); root.mainloop()

if __name__ == "__main__":
    main()
