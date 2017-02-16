#include "slang.h"
#include <histedit.h>
#include <cstdio>

using namespace std;
using namespace slang;

const char *prompt(EditLine *e) {
    return " > ";
}

const char *promptMultiline(EditLine *e) {
    return ".. ";
}

int main(int argc, char *argv[]) {
    ScriptSession session(true);
    EditLine *el;
    History *cmdHistory;
    HistEvent ev;

    el = el_init(argv[0], stdin, stdout, stderr);
    ASSERT(el);
    el_set(el, EL_PROMPT, &prompt);

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
            if (charsRead) {
                history(cmdHistory, &ev, H_ENTER, line);
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

        try {
            auto value = session.evalWithKind(snippet);
            printf("Detected kind: %s\n", get<1>(value).c_str());
            const SVInt *integer = get_if<SVInt>(&get<0>(value));
            if (integer) {
                printf("Integer value: %d\n", integer->getAssertUInt16());
            }
        } catch (Diagnostics &diags) {
            printf("Errors when parsing:\n");
            printf("%s\n", diagWriter.report(diags).c_str());
        }
    }
    return 0;
}
