#include "slang/diagnostics/DiagnosticClient.h"
#include "pyslang.h"
//
using namespace slang;
class PyDiagnosticClient : public DiagnosticClient {
public:
    /* Inherit the constructors */
    using DiagnosticClient::DiagnosticClient;

    void report(const ReportedDiagnostic& diagnostic) override {
        PYBIND11_OVERRIDE_PURE(void, DiagnosticClient, report, diagnostic);    
    };

    void setEngine(const DiagnosticEngine& engine) {
        PYBIND11_OVERRIDE(void,  DiagnosticClient,  setEngine,  engine);
    };
};
