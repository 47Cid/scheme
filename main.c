#include "mpc/mpc.h"

#include <editline/readline.h>

struct val;
struct env;
typedef struct val val;
typedef struct env env;

enum { ERR, NUM, SYM, FUN, SEXPR, QEXPR };

typedef val *(*builtin)(env *, val *);

struct val {
  int type;

  long num;
  char *err;
  char *sym;

  builtin builtin;
  env *env;
  val *formals;
  val *body;

  int count;
  val **cell;
};

val *val_num(long x) {
  val *v = malloc(sizeof(val));
  v->type = NUM;
  v->num = x;
  return v;
}

val *val_err(char *fmt, ...) {
  val *v = malloc(sizeof(val));
  v->type = ERR;
  va_list va;
  va_start(va, fmt);
  v->err = malloc(512);
  vsnprintf(v->err, 511, fmt, va);
  v->err = realloc(v->err, strlen(v->err) + 1);
  va_end(va);
  return v;
}

val *val_sym(char *s) {
  val *v = malloc(sizeof(val));
  v->type = SYM;
  v->sym = malloc(strlen(s) + 1);
  strcpy(v->sym, s);
  return v;
}

val *val_builtin(builtin func) {
  val *v = malloc(sizeof(val));
  v->type = FUN;
  v->builtin = func;
  return v;
}

env *env_new(void);

val *val_lambda(val *formals, val *body) {
  val *v = malloc(sizeof(val));
  v->type = FUN;

  v->builtin = NULL;

  v->env = env_new();

  v->formals = formals;
  v->body = body;
  return v;
}

val *val_sexpr(void) {
  val *v = malloc(sizeof(val));
  v->type = SEXPR;
  v->count = 0;
  v->cell = NULL;
  return v;
}

val *val_qexpr(void) {
  val *v = malloc(sizeof(val));
  v->type = QEXPR;
  v->count = 0;
  v->cell = NULL;
  return v;
}

void env_del(env *e);

void val_del(val *v) {

  switch (v->type) {
  case NUM:
    break;
  case FUN:
    if (!v->builtin) {
      env_del(v->env);
      val_del(v->formals);
      val_del(v->body);
    }
    break;
  case ERR:
    free(v->err);
    break;
  case SYM:
    free(v->sym);
    break;
  case QEXPR:
  case SEXPR:
    for (int i = 0; i < v->count; i++) {
      val_del(v->cell[i]);
    }
    free(v->cell);
    break;
  }

  free(v);
}

env *env_copy(env *e);

val *val_copy(val *v) {
  val *x = malloc(sizeof(val));
  x->type = v->type;
  switch (v->type) {
  case FUN:
    if (v->builtin) {
      x->builtin = v->builtin;
    } else {
      x->builtin = NULL;
      x->env = env_copy(v->env);
      x->formals = val_copy(v->formals);
      x->body = val_copy(v->body);
    }
    break;
  case NUM:
    x->num = v->num;
    break;
  case ERR:
    x->err = malloc(strlen(v->err) + 1);
    strcpy(x->err, v->err);
    break;
  case SYM:
    x->sym = malloc(strlen(v->sym) + 1);
    strcpy(x->sym, v->sym);
    break;
  case SEXPR:
  case QEXPR:
    x->count = v->count;
    x->cell = malloc(sizeof(val *) * x->count);
    for (int i = 0; i < x->count; i++) {
      x->cell[i] = val_copy(v->cell[i]);
    }
    break;
  }
  return x;
}

val *val_add(val *v, val *x) {
  v->count++;
  v->cell = realloc(v->cell, sizeof(val *) * v->count);
  v->cell[v->count - 1] = x;
  return v;
}

val *val_join(val *x, val *y) {
  for (int i = 0; i < y->count; i++) {
    x = val_add(x, y->cell[i]);
  }
  free(y->cell);
  free(y);
  return x;
}

val *val_pop(val *v, int i) {
  val *x = v->cell[i];
  memmove(&v->cell[i], &v->cell[i + 1], sizeof(val *) * (v->count - i - 1));
  v->count--;
  v->cell = realloc(v->cell, sizeof(val *) * v->count);
  return x;
}

val *val_take(val *v, int i) {
  val *x = val_pop(v, i);
  val_del(v);
  return x;
}

void val_print(val *v);

void val_print_expr(val *v, char open, char close) {
  putchar(open);
  for (int i = 0; i < v->count; i++) {
    val_print(v->cell[i]);
    if (i != (v->count - 1)) {
      putchar(' ');
    }
  }
  putchar(close);
}

void val_print(val *v) {
  switch (v->type) {
  case FUN:
    if (v->builtin) {
      printf("<builtin>");
    } else {
      printf("(\\ ");
      val_print(v->formals);
      putchar(' ');
      val_print(v->body);
      putchar(')');
    }
    break;
  case NUM:
    printf("%li", v->num);
    break;
  case ERR:
    printf("Error: %s", v->err);
    break;
  case SYM:
    printf("%s", v->sym);
    break;
  case SEXPR:
    val_print_expr(v, '(', ')');
    break;
  case QEXPR:
    val_print_expr(v, '{', '}');
    break;
  }
}

void val_println(val *v) {
  val_print(v);
  putchar('\n');
}

char *type_name(int t) {
  switch (t) {
  case FUN:
    return "Function";
  case NUM:
    return "Number";
  case ERR:
    return "Error";
  case SYM:
    return "Symbol";
  case SEXPR:
    return "S-Expression";
  case QEXPR:
    return "Q-Expression";
  default:
    return "Unknown";
  }
}

/* Environment */

struct env {
  env *par;
  int count;
  char **syms;
  val **vals;
};

env *env_new(void) {
  env *e = malloc(sizeof(env));
  e->par = NULL;
  e->count = 0;
  e->syms = NULL;
  e->vals = NULL;
  return e;
}

void env_del(env *e) {
  for (int i = 0; i < e->count; i++) {
    free(e->syms[i]);
    val_del(e->vals[i]);
  }
  free(e->syms);
  free(e->vals);
  free(e);
}

env *env_copy(env *e) {
  env *n = malloc(sizeof(env));
  n->par = e->par;
  n->count = e->count;
  n->syms = malloc(sizeof(char *) * n->count);
  n->vals = malloc(sizeof(val *) * n->count);
  for (int i = 0; i < e->count; i++) {
    n->syms[i] = malloc(strlen(e->syms[i]) + 1);
    strcpy(n->syms[i], e->syms[i]);
    n->vals[i] = val_copy(e->vals[i]);
  }
  return n;
}

val *env_get(env *e, val *k) {

  for (int i = 0; i < e->count; i++) {
    if (strcmp(e->syms[i], k->sym) == 0) {
      return val_copy(e->vals[i]);
    }
  }

  if (e->par) {
    return env_get(e->par, k);
  } else {
    return val_err("Unbound Symbol '%s'", k->sym);
  }
  
}

void env_put(env *e, val *k, val *v) {

  for (int i = 0; i < e->count; i++) {
    if (strcmp(e->syms[i], k->sym) == 0) {
      val_del(e->vals[i]);
      e->vals[i] = val_copy(v);
      return;
    }
  }

  e->count++;
  e->vals = realloc(e->vals, sizeof(val *) * e->count);
  e->syms = realloc(e->syms, sizeof(char *) * e->count);
  e->vals[e->count - 1] = val_copy(v);
  e->syms[e->count - 1] = malloc(strlen(k->sym) + 1);
  strcpy(e->syms[e->count - 1], k->sym);
}

void env_def(env *e, val *k, val *v) {
  while (e->par) {
    e = e->par;
  }
  env_put(e, k, v);
}

/* Builtins */

val *val_eval(env *e, val *v);

val *builtin_lambda(env *e, val *a) {
  val *formals = val_pop(a, 0);
  val *body = val_pop(a, 0);
  val_del(a);
  return val_lambda(formals, body);
}

val *builtin_list(env *e, val *a) {
  a->type = QEXPR;
  return a;
}

val *builtin_eval(env *e, val *a) {
  val *x = val_take(a, 0);
  x->type = SEXPR;
  return val_eval(e, x);
}

val *builtin_op(env *e, val *a, char *op) {
  val *x = val_pop(a, 0);

  if ((strcmp(op, "-") == 0) && a->count == 0) {
    x->num = -x->num;
  }

  while (a->count > 0) {
    val *y = val_pop(a, 0);

    if (strcmp(op, "+") == 0) {
      x->num += y->num;
    }
    if (strcmp(op, "-") == 0) {
      x->num -= y->num;
    }
    if (strcmp(op, "*") == 0) {
      x->num *= y->num;
    }
    if (strcmp(op, "/") == 0) {
      if (y->num == 0) {
        val_del(x);
        val_del(y);
        x = val_err("Division By Zero.");
        break;
      }
      x->num /= y->num;
    }

    val_del(y);
  }

  val_del(a);
  return x;
}

val *builtin_add(env *e, val *a) { return builtin_op(e, a, "+"); }
val *builtin_mul(env *e, val *a) { return builtin_op(e, a, "*"); }

val *builtin_var(env *e, val *a, char *func) {

  val *syms = a->cell[0];

  for (int i = 0; i < syms->count; i++) {
    if (strcmp(func, "def") == 0) {
      env_def(e, syms->cell[i], a->cell[i + 1]);
    }
  }

  val_del(a);
  return val_sexpr();
}

val *builtin_def(env *e, val *a) { return builtin_var(e, a, "def"); }

void env_add_builtin(env *e, char *name, builtin func) {
  val *k = val_sym(name);
  val *v = val_builtin(func);
  env_put(e, k, v);
  val_del(k);
  val_del(v);
}

void env_add_builtins(env *e) {
  env_add_builtin(e, "lambda", builtin_lambda);
  env_add_builtin(e, "def", builtin_def);

  env_add_builtin(e, "+", builtin_add);
  env_add_builtin(e, "*", builtin_mul);
}

/* Evaluation */

val *val_call(env *e, val *f, val *a) {
  if (f->builtin) {
    return f->builtin(e, a);
  }
  int given = a->count;
  int total = f->formals->count;

  while (a->count) {
    if (f->formals->count == 0) {
      val_del(a);
      return val_err("Function passed too many arguments. "
                      "Got %i, Expected %i.",
                      given, total);
    }

    val *sym = val_pop(f->formals, 0);

    if (strcmp(sym->sym, "&") == 0) {

      if (f->formals->count != 1) {
        val_del(a);
        return val_err("Function format invalid. "
                        "Symbol '&' not followed by single symbol.");
      }

      val *nsym = val_pop(f->formals, 0);
      env_put(f->env, nsym, builtin_list(e, a));
      val_del(sym);
      val_del(nsym);
      break;
    }
    val *val = val_pop(a, 0);
    env_put(f->env, sym, val);

    val_del(sym);
    val_del(val);
  }

  val_del(a);

  if (f->formals->count == 0) {
    f->env->par = e;
    return builtin_eval(f->env, val_add(val_sexpr(), val_copy(f->body)));
  } else {
    return val_copy(f);
  }
}

val *val_eval_sexpr(env *e, val *v) {
  for (int i = 0; i < v->count; i++) {
    v->cell[i] = val_eval(e, v->cell[i]);
  }

  for (int i = 0; i < v->count; i++) {
    if (v->cell[i]->type == ERR) {
      return val_take(v, i);
    }
  }

  if (v->count == 0) {
    return v;
  }
  if (v->count == 1) {
    return val_eval(e, val_take(v, 0));
  }

  val *f = val_pop(v, 0);
  val *result = val_call(e, f, v);
  val_del(f);
  return result;
}

val *val_eval(env *e, val *v) {
  if (v->type == SYM) {
    val *x = env_get(e, v);
    val_del(v);
    return x;
  }
  if (v->type == SEXPR) {
    return val_eval_sexpr(e, v);
  }
  return v;
}

/* Reading */

val *val_read_num(mpc_ast_t *t) {
  long x = strtol(t->contents, NULL, 10);
  return val_num(x);
}

val *val_read(mpc_ast_t *t) {

  if (strstr(t->tag, "number")) {
    return val_read_num(t);
  }
  if (strstr(t->tag, "symbol")) {
    return val_sym(t->contents);
  }

  val *x = NULL;
  if (strcmp(t->tag, ">") == 0) {
    x = val_sexpr();
  }
  if (strstr(t->tag, "sexpr")) {
    x = val_sexpr();
  }
  if (strstr(t->tag, "qexpr")) {
    x = val_qexpr();
  }

  for (int i = 0; i < t->children_num; i++) {
    if (strcmp(t->children[i]->contents, "(") == 0) {
      continue;
    }
    if (strcmp(t->children[i]->contents, ")") == 0) {
      continue;
    }
    if (strcmp(t->children[i]->contents, "}") == 0) {
      continue;
    }
    if (strcmp(t->children[i]->contents, "{") == 0) {
      continue;
    }
    if (strcmp(t->children[i]->tag, "regex") == 0) {
      continue;
    }
    x = val_add(x, val_read(t->children[i]));
  }

  return x;
}

/* Main */

int main(int argc, char **argv) {
  mpc_parser_t *Number = mpc_new("number");
  mpc_parser_t *Symbol = mpc_new("symbol");
  mpc_parser_t *Atom = mpc_new("atom");
  mpc_parser_t *Sexpr = mpc_new("sexpr");
  mpc_parser_t *Qexpr = mpc_new("qexpr");
  mpc_parser_t *Expr = mpc_new("expr");
  mpc_parser_t *Top = mpc_new("top");

  mpca_lang(MPCA_LANG_DEFAULT, "                                             \
      number : /-?[0-9]+/ ;                               \
      symbol : /[a-zA-Z0-9_+\\-*\\/\\\\=<>!&]+/ ;        \
      atom   : <number> | <symbol> | <qexpr> ;           \
      sexpr  : '(' <expr>* ')' ;                          \
      qexpr  : '{' <expr>* '}' ;                          \
      expr   : <number> | <symbol> | <sexpr> | <qexpr> ;  \
      top    : /^/ <atom> /$/ | /^/ <sexpr> /$/ ;         \
    ",
            Number, Symbol, Atom, Sexpr, Qexpr, Expr, Top);

  env *e = env_new();
  env_add_builtins(e);

  while (1) {
    char *input = readline(">> ");
    add_history(input);

    mpc_result_t r;
    if (mpc_parse("<stdin>", input, Top, &r)) {
      val *x = val_eval(e, val_read(r.output));
      val_println(x);
      val_del(x);
      mpc_ast_delete(r.output);
    } else {
      mpc_err_print(r.error);
      mpc_err_delete(r.error);
    }
    free(input);
  }
  env_del(e);
  mpc_cleanup(7, Number, Symbol, Atom, Sexpr, Qexpr, Expr, Top);
  return 0;
}
