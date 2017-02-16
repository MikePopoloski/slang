#include "slang.h"
#include <histedit.h>
#include <cstdio>

using namespace std;
using namespace slang;


const char *prompt(EditLine *e) {
    return " > ";
}

int main(int argc, char *argv[]) {
    ScriptSession session;
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

    /*
    BumpAllocator alloc;
    Diagnostics diagnostics;
    SourceManager& srcMgr = SyntaxTree::getDefaultSourceManager();
    Preprocessor preprocessor(srcMgr, alloc, diagnostics);
    */

    DiagnosticWriter diagWriter(SyntaxTree::getDefaultSourceManager());
    while (true) {
        line = el_gets(el, &charsRead);
        if (charsRead) {
            history(cmdHistory, &ev, H_ENTER, line);
        }
        /*
        preprocessor.pushSource(srcMgr.assignText(line));
        Parser parser(preprocessor);
        */
        try {
            auto value = session.evalWithKind(line);
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
