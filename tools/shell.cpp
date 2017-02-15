#include "slang.h"
#include <iostream>
#include <string>
#include <variant>

using namespace std;
using namespace slang;

int main(int argc, char *argv[]) {
    ScriptSession session;
    while (true) {
        string cmd;
        cout << " >>> ";
        getline(cin, cmd);
        auto value = session.eval(cmd);
        const SVInt *integer = get_if<SVInt>(&value);
        if (integer) {
            cout << "Integer value: " << *integer << endl;
        }
    }
    return 0;
}
