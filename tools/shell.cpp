#include "slang.h"
#include <histedit.h>
#include <cstdio>

using namespace std;
using namespace slang;

EditLine *el;
History *cmdHistory;

const char *prompt(EditLine *e)          { return " > "; }
const char *promptMultiline(EditLine *e) { return ".. "; }

void cleanup() {
    history_end(cmdHistory);
    el_end(el);
}

void onSignal(int sig) {
    cleanup();
    _Exit(sig);
}

int main(int argc, char *argv[]) {
    ScriptSession session(true);
    HistEvent ev;

    signal(SIGINT, onSignal);
    signal(SIGTSTP, onSignal);
    el = el_init(argv[0], stdin, stdout, stderr);
    ASSERT(el);
    el_set(el, EL_PROMPT, &prompt);
    el_set(el, EL_EDITOR, "emacs");

    cmdHistory = history_init();
    ASSERT(cmdHistory);
    history(cmdHistory, &ev, H_SETSIZE, 1000);
    el_set(el, EL_HIST, history, cmdHistory);

    int charsRead;
    const char *line;

    DiagnosticWriter diagWriter(SyntaxTree::getDefaultSourceManager());
    while (true) {
        string snippet;
        while (true) {
            line = el_gets(el, &charsRead);
            if (!line) {
                onSignal(SIGINT);
            }
            snippet += line;
            el_set(el, EL_PROMPT, &promptMultiline);
            if (snippet.size() > 2 && snippet[snippet.size()-2] == '\\') {
                snippet.erase(snippet.size()-2, 1);
            } else {
                break;
            }
        }
        el_set(el, EL_PROMPT, &prompt);
        if (snippet == "\n") {
            continue;
        } else {
            history(cmdHistory, &ev, H_ENTER, snippet.c_str());
        }

        try {
            auto value = session.evalWithKind(snippet);
            printf("Detected kind: %s\n", get<1>(value).c_str());
            const SVInt *integer = get_if<SVInt>(&get<0>(value));
            if (integer) {
                if (!integer->isSingleWord()) {
                    printf("Value (binary): %s\n", integer->toString(LiteralBase::Binary).c_str());
                } else {
                    printf("Value: %lld\n", integer->getAssertInt64());
                }
            }
        } catch (Diagnostics &diags) {
            printf("Errors when parsing:\n");
            printf("%s\n", diagWriter.report(diags).c_str());
        }
    }

    return 0;
}
