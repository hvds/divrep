#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include "coul.h"
#include "coulvec.h"
#include "coultau.h"
#include "coulfact.h"

/* from MPUG */
#include "utility.h"

/* FIXME: work out where these should be declared */
extern bool debugv, debugV;
static inline mpz_t *PARAM_TO_PTR(__mpz_struct *z) {
    return (mpz_t *)z;
}

mpz_t temp;

/* resizable list of uints */
typedef struct s_sui {
    uint size;
    uint count;
    uint *ui;
} t_sui;

/* constraints for a single modulus */
typedef struct s_cvec {
    uint modulus;
    uint count;         /* count of disallowed values */
    uint unfixed_count; /* count of unfixed disallowed values */
    uint unique_count;  /* count of uniquely disallowed values */
    uint unique_merged; /* unique count including merged */
    uint modval;        /* fixed value if in_mult */
    bool in_mult;       /* TRUE if included in overall modulus */
    char *v;            /* vector of disallowed values */
    char *vu;           /* vector of uniquely disallowed values */
    char *vum;          /* vector of uniquely disallowed including merged */
    t_sui div;          /* list of immediate divisors of this modulus */
    t_sui mult;         /* list of immediate multiples of this modulus */
    double potency;     /* ratio uniquely disallowed including merged */
} t_cvec;

/* typedef struct s_context t_context (in header) */
/* constraints for all moduli */
struct s_context {
    uint n;
    uint k;
    mpz_t *min;         /* requested minimum d, passed in */
    uint *target_t;     /* vector of (remaining) tau */
    t_cvec **vec;       /* modular constraints: vec[m] is mod m */
    uint nvec;
    mpz_t mod_mult;     /* fixed moduli: d == mod_mult (mod mult) */
    mpz_t mult;
    uint *sc;           /* list of packed moduli */
    uint *sc_add;       /* sc_add/mult used by prep_test/test_prepped */
    uint *sc_mult;
    uint sc_size;
    uint sc_count;      /* number of active packed moduli */
};

char *vresidues = NULL;
uint nvresidues = 0;

/* a single pending constraint: v !== offset (mod modulus) */
typedef struct s_suppress {
    uint modulus;
    uint offset;
    bool depend;
} t_suppress;
t_suppress *suppress_stack = NULL;
uint suppress_count = 0;
uint suppress_size = 0;

#if defined(TYPE_o) || defined(TYPE_r)
    static inline uint TYPE_OFFSET(t_context *cx, uint i) {
        return i;
    }
#elif defined(TYPE_a)
    static inline uint TYPE_OFFSET(t_context *cx, uint i) {
        return i * cx->n;
    }
#else
#   error "No type defined"
#endif

void *mem_dup(void *src, uint size) {
    void *dest = malloc(size);
    memcpy(dest, src, size);
    return dest;
}

t_context *cvec_init(uint n, uint k, mpz_t *min, uint *target_t) {
    t_context *cx = malloc(sizeof(t_context));
    cx->n = n;
    cx->k = k;
    cx->min = min;
    cx->target_t = target_t;
    cx->vec = NULL;
    cx->nvec = 0;
    mpz_init_set_ui(cx->mod_mult, 0);
    mpz_init_set_ui(cx->mult, 1);
    cx->sc = NULL;
    cx->sc_add = NULL;
    cx->sc_mult = NULL;
    cx->sc_size = 0;
    cx->sc_count = 0;
    mpz_init(temp);
    return cx;
}

void ctx_free(t_context *cx) {
    for (uint i = 0; i < cx->nvec; ++i) {
        t_cvec *cv = cx->vec[i];
        if (!cv)
            continue;
        free(cv->v);
        free(cv->vu);
        free(cv->vum);
        free(cv->div.ui);
        free(cv->mult.ui);
        free(cv);
    }
    free(cx->vec);
    mpz_clear(cx->mod_mult);
    mpz_clear(cx->mult);
    free(cx->sc);
    free(cx->sc_add);
    free(cx->sc_mult);
    free(cx);
}

void cvec_done(t_context *cx) {
    ctx_free(cx);
    free(vresidues);
    free(suppress_stack);
    mpz_clear(temp);
}

static inline void fail_402(uint m) {
    report("402 Error: all values (mod %u) disallowed (%.3fs)\n", m, elapsed());
    fail_silent();
}

/* size in bytes */
static inline uint vecsize(uint m) {
    return (m + 7) >> 3;
}

static inline uint VECOFF(uint off) {
    return off >> 3;
}
static inline char VECBIT(uint off) {
    return 1 << (off & 7);
}

static inline bool TESTBIT(char *v, uint off) {
    return (v[VECOFF(off)] & VECBIT(off)) ? 1 : 0;
}

static inline void SETBIT(char *v, uint off) {
    v[VECOFF(off)] |= VECBIT(off);
}

static inline void CLRBIT(char *v, uint off) {
    v[VECOFF(off)] &= ~VECBIT(off);
}

static inline uint mod(int i, int m) {
    int v = i % m;
    return (v < 0) ? m + v : v;
}

static inline double potency(uint modulus, uint count, uint unique) {
    uint avail = modulus - (count - unique);
    return (double)avail / (double)(avail - unique);
}

t_cvec **vec_dup(t_cvec **src, uint size) {
    t_cvec **dest = malloc(size * sizeof(t_cvec *));
    for (uint i = 0; i < size; ++i) {
        t_cvec *si = src[i];
        if (si == NULL) {
            dest[i] = NULL;
            continue;
        }
        t_cvec *di = mem_dup(si, sizeof(t_cvec));
        di->v = mem_dup(si->v, vecsize(i));
        di->vu = mem_dup(si->vu, vecsize(i));
        di->vum = mem_dup(si->vum, vecsize(i));
        di->div.ui = mem_dup(si->div.ui, si->div.count * sizeof(uint));
        di->div.size = di->div.count;
        di->mult.ui = mem_dup(si->mult.ui, si->mult.count * sizeof(uint));
        di->mult.size = di->mult.count;
        dest[i] = di;
    }
    return dest;
}

t_context *ctx_dup(t_context *cx) {
    t_context *cy = malloc(sizeof(t_context));
    cy->n = cx->n;
    cy->k = cx->k;
    cy->min = cx->min;
    cy->target_t = cx->target_t;
    cy->vec = vec_dup(cx->vec, cx->nvec);
    cy->nvec = cx->nvec;
    mpz_init_set(cy->mod_mult, cx->mod_mult);
    mpz_init_set(cy->mult, cx->mult);
    cy->sc = NULL;
    cy->sc_add = NULL;
    cy->sc_mult = NULL;
    cy->sc_size = 0;
    cy->sc_count = 0;
    return cy;
}

char *residues(uint m) {
    if (vecsize(m) > nvresidues) {
        free(vresidues);
        vresidues = calloc(vecsize(m), sizeof(char));
        nvresidues = vecsize(m);
    } else {
        memset(vresidues, 0, vecsize(m));
    }
    for (uint i = 0; i <= (m >> 1); ++i)
        SETBIT(vresidues, (i * i) % m);
    return vresidues;
}

void add_sui(t_sui *suip, uint v) {
    if (suip->count + 1 >= suip->size) {
        uint size = suip->size + 10;
        suip->ui = realloc(suip->ui, size * sizeof(uint));
        suip->size = size;
    }
    suip->ui[suip->count++] = v;
}

void mult_combine(t_context *cx, mpz_t modulus, mpz_t offset) {
    mpz_t zarray[4];
    mpz_t *modp = PARAM_TO_PTR(modulus);
    mpz_t *offp = PARAM_TO_PTR(offset);
    memcpy(&zarray[0], cx->mod_mult, sizeof(mpz_t));
    memcpy(&zarray[1], *offp, sizeof(mpz_t));
    memcpy(&zarray[2], cx->mult, sizeof(mpz_t));
    memcpy(&zarray[3], *modp, sizeof(mpz_t));
    if (!chinese(cx->mod_mult, cx->mult, &zarray[0], &zarray[2], 2))
        fail("chinese");
}

void mult_combine_ui(t_context *cx, uint modulus, uint offset) {
    mpz_t off, mod;
    mpz_init_set_ui(off, offset);
    mpz_init_set_ui(mod, modulus);
    mult_combine(cx, mod, off);
    mpz_clear(off);
    mpz_clear(mod);
}

void resize_cvec(t_context *cx, uint size) {
    if (size < cx->nvec)
        return;
    uint newsize = cx->nvec ? (cx->nvec * 3 / 2) : 100;
    if (size >= newsize)
        newsize = size + 1;
    cx->vec = realloc(cx->vec, newsize * sizeof(t_cvec *));
    for (uint i = cx->nvec; i < newsize; ++i)
        cx->vec[i] = NULL;
    cx->nvec = newsize;
}

t_cvec *new_cvec(t_context *cx, uint m);
static inline t_cvec *get_cvec(t_context *cx, uint m) {
    if (m < cx->nvec && cx->vec[m])
        return cx->vec[m];
    return new_cvec(cx, m);
}
static inline t_cvec *get_if_cvec(t_context *cx, uint m) {
    if (m < cx->nvec && cx->vec[m])
        return cx->vec[m];
    return NULL;
}

t_cvec *new_cvec(t_context *cx, uint m) {
    if (m >= cx->nvec)
        resize_cvec(cx, m);
    t_cvec *cv = calloc(1, sizeof(t_cvec));
    cx->vec[m] = cv;
    uint vsize = vecsize(m);
    cv->modulus = m;
    cv->v = calloc(vsize, sizeof(char));
    cv->vu = calloc(vsize, sizeof(char));
    cv->vum = calloc(vsize, sizeof(char));
    char *v = cv->v;

    t_fact f;
    init_fact(&f);
    simple_fact(m, &f);
    for (uint fi = 0; fi < f.count; ++fi) {
        uint mp = f.ppow[fi].p;
        uint md = m / mp;
        t_cvec *cvd = get_cvec(cx, md);
        add_sui(&cv->div, md);
        add_sui(&cvd->mult, m);
        if (cvd->count == 0)
            continue;
        char *vd = cvd->v;
        for (uint j = 0; j < md; ++j) {
            if ((cvd->in_mult) ? (j == cvd->modval) : !TESTBIT(vd, j))
                continue;
            for (uint k = 0; k < mp; ++k) {
                uint jk = k * md + j;
                if (TESTBIT(v, jk))
                    continue;
                if (debugV)
                    printf("init %u (mod %u) from %u (mod %u)\n",
                            jk, m, j, md);
                SETBIT(v, jk);
                ++cv->count;
            }
        }
    }
    free_fact(&f);

    /* new cvec is initialized, now check for cross-propagation */
    if (cv->div.count > 1) {
        for (uint di = 0; di < cv->div.count; ++di) {
            uint md = cv->div.ui[di];
            uint mp = m / md;
            t_cvec *cvd = get_cvec(cx, md);
            char *vd = cvd->v;
            for (uint j = 0; j < md; ++j) {
                if (TESTBIT(vd, j))
                    continue;
                for (uint k = 0; k < mp; ++k)
                    if (!TESTBIT(v, k * md + j))
                        goto no_propagate;
                suppress(cx, md, j, 0);
                /* FIXME: short-circuit */
              no_propagate:
                ;
            }
        }
    }
    return cv;
}

/* we know the value is fixed to be == v (mod m), so make sure that is
 * marked in mult/mod_mult, and propagate */
void fix_cvec(t_context *cx, uint m, uint v) {
    t_cvec *cv = get_cvec(cx, m);
    if (cv->in_mult) {
        if (v != cv->modval)
            fail_402(m);
        return;
    }

    if (TESTBIT(cv->v, v))
        fail_402(m);
    cv->modval = v;
    cv->count = m - 1;
    mult_combine_ui(cx, m, v);
    cv->in_mult = 1;

    if (debugv)
        report("fix %u (mod %u) giving %Zu (mod %Zu)\n",
                v, m, cx->mod_mult, cx->mult);

    t_sui *div = &cv->div;
    for (int i = 0; i < div->count; ++i) {
        uint d = div->ui[i];
        if (d > 1)
            fix_cvec(cx, d, v % d);
    }
}

/* constraint the value to be !== v (mod m)
   if (depend) then this is not unique, ie there is some d > 1: m = dm'
   such that we already constrain !== v (mod m')
*/
void suppress(t_context *cx, uint m, uint v, bool depend) {
    if (suppress_count + 1 >= suppress_size) {
        uint newsize = suppress_size ? (suppress_size * 3 / 2) : 100;
        suppress_stack = realloc(suppress_stack, newsize * sizeof(t_suppress));
        suppress_size = newsize;
    }
    uint ssi = suppress_count++;
    t_suppress *ssp = &suppress_stack[ssi];
    ssp->modulus = m;
    ssp->offset = v;
    ssp->depend = depend;
    if (ssi > 0) {
        /* this isn't the first, let the stack unwind to the top-level
         * recurse and handle it there */
        return;
    }

    while (suppress_count) {
        ssi = --suppress_count;
        ssp = &suppress_stack[ssi];
        m = ssp->modulus;
        v = ssp->offset;
        depend = ssp->depend;

        t_cvec *cm = get_cvec(cx, m);
        if (cm->in_mult) {
            if (v == cm->modval)
                fail_402(m);
            /* nothing to do */
            continue;
        }
        if (depend) {
            if (TESTBIT(cm->vu, v)) {
                if (debugV)
                    printf("suppress %u (mod %u), now dependent\n", v, m);
                CLRBIT(cm->vu, v);
                --cm->unique_count;
            }
            if (TESTBIT(cm->v, v))
                continue;   /* no effect to propagate */
        } else {
            if (TESTBIT(cm->v, v))
                continue;   /* no effect to propagate */
            if (debugV)
                printf("suppress %u (mod %u), is independent\n", v, m);
            SETBIT(cm->vu, v);
            ++cm->unique_count;
        }
        if (debugV)
            printf("suppress %u (mod %u), is set\n", v, m);
        SETBIT(cm->v, v);
        ++cm->count;
        if (cm->count >= cm->modulus - 1) {
            /* should not be possible */
            if (cm->count >= cm->modulus)
                fail_402(m);
            uint last = m;
            for (uint i = 0; i < m; ++i) {
                if (TESTBIT(cm->v, i))
                    continue;
                last = i;
                break;
            }
            if (last >= m)
                fail("logic error");
            fix_cvec(cx, m, last);
        }

        for (uint i = 0; i < cm->mult.count; ++i) {
            uint mp = cm->mult.ui[i];
            uint d = mp / m;
            for (uint j = 0; j < d; ++j)
                suppress(cx, mp, m * j + v, 1);
        }

        for (uint i = 0; i < cm->div.count; ++i) {
            uint d = cm->div.ui[i];
            uint p = m / d;
            uint dv = v % d;
            for (uint j = 0; j < p; ++j)
                if (!TESTBIT(cm->v, d * j + dv))
                    goto next_suppress_divisor;
            for (uint j = 0; j < p; ++j) {
                uint mdv = d * j + dv;
                if (!TESTBIT(cm->vu, mdv))
                    continue;
                if (debugV)
                    printf("suppress %u (mod %u), propagate\n", mdv, m);
                CLRBIT(cm->vu, mdv);
                --cm->unique_count;
            }
            suppress(cx, d, dv, 0);
          next_suppress_divisor:
            ;
        }
    }
}

/* apply an external positive or negative modular constraint,
 * restricting constraint vectors to use moduli only up to limit
 * (for positive constraints).
 */
void apply_modfix(t_context *cx, mpz_t m, mpz_t v, bool negate, uint limit) {
    mpz_mod(v, v, m);
    if (negate) {
        if (!mpz_fits_uint_p(m))
            fail("negated modulus %Zu is too large");
        suppress(cx, mpz_get_ui(m), mpz_get_ui(v), 0);
        return;
    }
    /* positive: require v (mod m) for factors up to limit, force
     * mult for the rest */
    if (mpz_cmp_ui(m, limit) <= 0) {
        uint um = mpz_get_ui(m);
        uint uv = mpz_get_ui(v);
        for (uint i = 0; i < um; ++i) {
            if (i == uv)
                continue;
            suppress(cx, um, uv, 0);
        }
        return;
    }
    factor_state fs;
    t_fact f;
    fs_init(&fs);
    init_fact(&f);
    mpz_set(fs.n, m);
    while (factor_one(&fs)) {
        if (mpz_cmp_ui(fs.f, limit) > 0)
            continue;
        t_ppow pp;
        pp.p = mpz_get_ui(fs.f);
        pp.e = fs.e;
        add_fact(&f, pp);
    }
    fs_clear(&fs);
    for (uint i = 0; i < f.count; ++i) {
        uint p = f.ppow[i].p;
        uint e = f.ppow[i].e;
        uint pp = p;
        uint plim = limit / p;
        uint prevval = 0;
        uint prevpp = 1;
        while (e--) {
            uint thisval = mpz_fdiv_ui(v, pp);
            for (uint j = 0; j < p; ++j) {
                uint jval = prevpp * j + prevval;
                if (jval == thisval)
                    continue;
                suppress(cx, pp, jval, 0);
            }
            if (pp > plim)
                break;
            prevpp = pp;
            pp *= p;
            prevval = thisval;
        }
    }
    free_fact(&f);
    mult_combine(cx, m, v);
}

/* Search for and apply constraints for modulus m (with factorization fm).
 */
void apply_m(t_context *cx, uint m, t_fact *fm) {
    uint tm = 1;    /* tau(m) */
    uint r = 1;     /* rad(m) */
    uint tmr = 1;   /* tau(m/r) */
    for (uint i = 0; i < fm->count; ++i) {
        t_ppow *pp = &fm->ppow[i];
        tm *= pp->e + 1;
        r *= pp->p;
        tmr *= pp->e;
    }
    uint mr = m / r;
    for (uint i = 0; i < cx->k; ++i) {
        uint di = TYPE_OFFSET(cx, i);
        uint ti = cx->target_t[i];
        /* tau(mx) > tau(m) for all x > 1 */
        /* TODO: if ti == tm, then walk_1() and suppress anyway */
/* FIXME: if v_k is fixed to a multiple of anything coprime to m,
 * we should compare a lower ti */
        if (ti < tm || (ti == tm && mpz_cmp_ui(*cx->min, (int)m - (int)di) > 0))
            suppress(cx, m, mod(-(int)di, m), 0);

        /* mx (mod m rad(m)) with (x, rad(m)) = 1 gives forced multiple */
        if ((mr % r) == 0 && (ti % tmr))
            for (uint j = 1; j < r; ++j)
                if (tiny_gcd(j, r) == 1)
                    suppress(cx, m, mod((int)mr * j - (int)di, m), 0);

        /* suppress all quadratic non-residues for square target */
        if (ti & 1) {
            char *res = residues(m);
            for (uint j = 0; j < m; ++j)
                if (!TESTBIT(res, j))
                    suppress(cx, m, mod((int)j - (int)di, m), 0);

            /* special-case p^6 + 1 factorization */
            /* FIXME: generalize to p^{2x} + a^{x} for odd x: 2x+1 prime */
            if (ti == 7 && i + 1 < cx->k && cx->target_t[i + 1] < 8
                && mpz_cmp_ui(*cx->min, 729 - i) > 0
            ) {
                report("402 Error: all values (mod %u) disallowed by p^6+1"
                        " factorization (%.3fs)\n", m, elapsed());
                fail_silent();
            }
        }
    }
}

void dump_sc(t_context *cx) {
    gmp_printf("fixed: %Zu (mod %Zu)\n", cx->mod_mult, cx->mult);
    for (uint i = 0; i < cx->sc_count; ++i) {
        uint mi = cx->sc[i];
        t_cvec *cv = get_if_cvec(cx, mi);
        if (!cv)
            fail("logic error, constraints for m=%u not available", mi);
        uint gi = mpz_gcd_ui(NULL, cx->mult, mi);
        printf("m=%u: mg=%u, c=%u, uc=%u, um=%u, pot=%.2f\n",
                mi, mi / gi, cv->unfixed_count, cv->unique_count,
                cv->unique_merged, cv->potency);
    }
}

void push_sc(t_context *cx, uint m) {
    if (cx->sc_count + 1 >= cx->sc_size) {
        uint newsize = cx->sc_size ? (cx->sc_size * 3 / 2) : 100;
        cx->sc = realloc(cx->sc, newsize * sizeof(uint));
        cx->sc_add = realloc(cx->sc_add, newsize * sizeof(uint));
        cx->sc_mult = realloc(cx->sc_mult, newsize * sizeof(uint));
        cx->sc_size = newsize;
    }
    cx->sc[cx->sc_count++] = m;
}

/* splice out by index */
static inline void splice_sci(t_context *cx, uint sci) {
    --cx->sc_count;
    uint scmove = cx->sc_count - sci;
    if (scmove)
        memmove(&cx->sc[sci], &cx->sc[sci + 1], scmove * sizeof(uint));
}
/* splice out by modulus, for index > sci */
static inline void splice_sc(t_context *cx, uint m, uint sci) {
    for (uint scj = sci + 1; scj < cx->sc_count; ++scj)
        if (cx->sc[scj] == m) {
            splice_sci(cx, scj);
            break;
        }
}

/* sort by potency descending */
t_context *sortcx;
int cmp_potency(const void *va, const void *vb) {
    uint a = *(uint *)va, b = *(uint *)vb;
    double pa = sortcx->vec[a]->potency, pb = sortcx->vec[b]->potency;
    return (pa > pb) ? -1 : (pa < pb) ? 1 : 0;
}

/* Pack vector for modulus ms into that for modulus md, given that md
 * is a multiple of ms.
 */
void cvec_merge(t_context *cx, uint md, uint ms) {
    if (debugv)
        printf("pack %u into %u\n", ms, md);
    t_cvec *cvd = get_cvec(cx, md);
    t_cvec *cvs = get_cvec(cx, ms);
    char *vums = cvs->vum;
    char *vumd = cvd->vum;
    uint p = md / ms;
    uint gd = mpz_gcd_ui(NULL, cx->mult, md);
    uint gmd = mpz_fdiv_ui(cx->mod_mult, gd);
    for (uint i = 0; i < ms; ++i) {
        if (!TESTBIT(vums, i))
            continue;
        for (uint j = 0; j < p; ++j) {
            uint off = j * ms + i;
            if ((off % gd) != gmd)
                continue;
            if (TESTBIT(vumd, off))
                continue;
            SETBIT(vumd, off);
            ++cvd->unique_merged;
        }
    }
    cvd->potency = potency(md / gd, cvd->unfixed_count, cvd->unique_merged);
}

/* Find active constraints; absorb into mod_mult where possible.
 */
void cvec_pack(t_context *cx, uint chunksize, double minratio) {
    cx->sc_count = 0;
    for (uint m = 2; m < cx->nvec; ++m) {
        t_cvec *cv = get_if_cvec(cx, m);
        if (!cv)
            continue;
        if (cv->in_mult)
            continue;
        if (cv->count == m)
            fail_402(m);
        if (cv->count == m - 1) {
            uint last;
            for (uint i = 0; i < m; ++i)
                if (!TESTBIT(cv->v, i)) {
                    last = i;
                    break;
                }
            fix_cvec(cx, m, last);
            continue;
        }
        uint g = mpz_gcd_ui(NULL, cx->mult, m);
        if (g > 1) {
            uint gm = mpz_fdiv_ui(cx->mod_mult, g);
            char *v = cv->v;
            uint uc = 0;
            for (uint i = 0; i < m / g; ++i) {
                uint vi = i * g + gm;
                if (TESTBIT(v, vi))
                    ++uc;
            }
            cv->unfixed_count = uc;
        } else
            cv->unfixed_count = cv->count;
        memcpy(cv->vum, cv->vu, vecsize(m));
        cv->unique_merged = cv->unique_count;
        /* using this modulus for a test will trap u / a of the inputs;
         * we call it a positive potency of a / (a - u) */
        cv->potency = potency(m / g, cv->unfixed_count, cv->unique_count);
        if (cv->unique_count)
            push_sc(cx, m);
    }

    /* optimize, combine, sort by potency */
    sortcx = cx;
    qsort(cx->sc, cx->sc_count, sizeof(uint), &cmp_potency);

    for (uint i = 0; i < cx->sc_count; ++i) {
      redo_mi: ;
        uint mi = cx->sc[i];
        for (uint j = i + 1; j < cx->sc_count; ++j) {
            uint mj = cx->sc[j];
            uint mij = mi * mj / tiny_gcd(mi, mj);
            if (mij > chunksize && mij > mi && mij > mj)
                continue;   /* too big to merge */
            /* splice [j] out of the list, then merge them */
            splice_sci(cx, j);
            if (mi == mij) {
                cvec_merge(cx, mi, mj);
            } else if (mj == mij) {
                cvec_merge(cx, mj, mi);
                cx->sc[i] = mj;
                goto redo_mi;
            } else {
                /* FIXME: we should be searching the combined vector for new
                 * fixed moduli to push to mult/mod_mult, but if we find any
                 * we'd essentially have to start again, which is a bother.
                 */
                cvec_merge(cx, mij, mi);
                cvec_merge(cx, mij, mj);
                cx->sc[i] = mij;
                splice_sc(cx, mij, i);
                goto redo_mi;
            }
        }
    }

    /* sort again */
    sortcx = cx;
    qsort(cx->sc, cx->sc_count, sizeof(uint), &cmp_potency);

    /* find the cutoff */
    if (minratio > 1.0)
        for (uint i = 0; i < cx->sc_count; ++i) {
            t_cvec *cv = cx->vec[ cx->sc[i] ];
            if (cv->potency >= minratio)
                continue;
            cx->sc_count = i;
            break;
        }

    if (debugv)
        dump_sc(cx);
}

/* Stores mult/mod_mult into the supplied mpz_t*; returns TRUE if there
 * is an effective fixed modulus.
 */
bool cvec_mult(t_context *cx, mpz_t *mod_mult, mpz_t *mult) {
    mpz_set(*mod_mult, cx->mod_mult);
    mpz_set(*mult, cx->mult);
    return mpz_cmp_ui(cx->mult, 1);
}

/* Returns TRUE if v is suppressed by any known constraint, else FALSE.
 */
bool cvec_testv(t_context *cx, mpz_t v) {
    for (uint i = 0; i < cx->sc_count; ++i) {
        uint m = cx->sc[i];
        t_cvec *cv = cx->vec[m];
        uint off = mpz_fdiv_ui(v, m);
        if (TESTBIT(cv->v, off))
            return 0;
    }
    return 1;
}

bool cvec_test(t_context *cx, mpz_t value, mpz_t *mod, mpz_t *mult) {
    mpz_mul(temp, *mult, value);
    mpz_add(temp, temp, *mod);
    return cvec_testv(cx, temp);
}

bool cvec_test_ui(t_context *cx, ulong value, mpz_t *mod, mpz_t *mult) {
    mpz_mul_ui(temp, *mult, value);
    mpz_add(temp, temp, *mod);
    return cvec_testv(cx, temp);
}

/* Initialize for multiple tests of numbers each of the form d = r_q + a_q v,
 * for fixed r_q (mult) and a_q (mod); subsequent calls to cvec_test_prepped()
 * pass in v.
 * FIXME: if prep finds sc_mult = 0, we can immediately look up whether
 * sc_add is suppressed: if it is the whole walk can be aborted; if not,
 * we can mark this modulus test to be skipped in cvec_test_prepped.
 */
void cvec_prep_test(t_context *cx, mpz_t *mod, mpz_t *mult) {
    for (uint i = 0; i < cx->sc_count; ++i) {
        uint m = cx->sc[i];
        cx->sc_mult[i] = mpz_fdiv_ui(*mult, m);
        cx->sc_add[i] = mpz_fdiv_ui(*mod, m);
    }
}
bool cvec_test_ui_prepped(t_context *cx, ulong value) {
    for (uint i = 0; i < cx->sc_count; ++i) {
        uint m = cx->sc[i];
        uint v = value % m;
        v = (v * cx->sc_mult[i] + cx->sc_add[i]) % m;
        t_cvec *cv = cx->vec[m];
        if (TESTBIT(cv->v, v))
            return 0;
    }
    return 1;
}
bool cvec_test_prepped(t_context *cx, mpz_t *value) {
    if (mpz_fits_ulong_p(*value))
        return cvec_test_ui_prepped(cx, mpz_get_ui(*value));

    for (uint i = 0; i < cx->sc_count; ++i) {
        uint m = cx->sc[i];
        uint v = mpz_fdiv_ui(*value, m);
        v = (v * cx->sc_mult[i] + cx->sc_add[i]) % m;
        t_cvec *cv = cx->vec[m];
        if (TESTBIT(cv->v, v))
            return 0;
    }
    return 1;
}
