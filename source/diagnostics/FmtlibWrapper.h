//------------------------------------------------------------------------------
// FmtlibWrapper.h
// Interfacing junk to glue fmtlib to DiagnosticWriter
//
// File is under the MIT license; see LICENSE for details.
//------------------------------------------------------------------------------
#pragma once

#include <flat_hash_map.hpp>
#include <fmt/ostream.h>

#include "slang/symbols/TypePrinter.h"

namespace format::detail {

using namespace slang;

// This machinery is to allow us to track state during formatting diagnostic arguments,
// and to share formatting options with a parent DiagonsticWriter. We rely on fmtlib to
// do the heavy lifting but want to hook into the operation at various points.
template<typename OutputIt>
class BasicFormatContext {
public:
    using char_type = char;

private:
    OutputIt out_;
    fmt::basic_format_args<BasicFormatContext> args_;
    fmt::internal::arg_map<BasicFormatContext> map_;
    fmt::internal::locale_ref loc_;

    BasicFormatContext(const BasicFormatContext&) = delete;
    void operator=(const BasicFormatContext&) = delete;

public:
    using iterator = OutputIt;
    using format_arg = fmt::basic_format_arg<BasicFormatContext>;
    template<typename T>
    using formatter_type = fmt::formatter<T, char_type>;

public:
    BasicFormatContext(OutputIt out, fmt::basic_format_args<BasicFormatContext> ctx_args,
                       fmt::internal::locale_ref loc = fmt::internal::locale_ref()) :
        out_(out),
        args_(ctx_args), loc_(loc) {}

    format_arg arg(int id) const { return args_.get(id); }
    format_arg arg(fmt::basic_string_view<char_type> name) {
        map_.init(args_);
        format_arg arg = map_.find(name);
        if (arg.type() == fmt::internal::none_type)
            this->on_error("argument not found");
        return arg;
    }

    fmt::internal::error_handler error_handler() { return {}; }
    void on_error(const char* message) { error_handler().on_error(message); }

    iterator out() { return out_; }

    void advance_to(iterator it) { out_ = it; }

    fmt::internal::locale_ref locale() { return loc_; }

    TypePrintingOptions* typeOptions;
    flat_hash_set<const Type*> seenTypes;
};

using FormatContext = BasicFormatContext<std::back_insert_iterator<fmt::internal::buffer<char>>>;

template<typename Range>
class ArgFormatter : public fmt::internal::arg_formatter_base<Range> {
private:
    using char_type = typename Range::value_type;
    using base = fmt::internal::arg_formatter_base<Range>;
    using context_type = BasicFormatContext<typename base::iterator>;

    context_type& ctx_;
    fmt::basic_format_parse_context<char_type>* parse_ctx_;

public:
    using range = Range;
    using iterator = typename base::iterator;
    using format_specs = typename base::format_specs;

    explicit ArgFormatter(context_type& ctx,
                          fmt::basic_format_parse_context<char_type>* parse_ctx = nullptr,
                          format_specs* spec = nullptr) :
        base(Range(ctx.out()), spec, ctx.locale()),
        ctx_(ctx), parse_ctx_(parse_ctx) {}

    using base::operator();

    iterator operator()(typename fmt::basic_format_arg<context_type>::handle handle) {
        handle.format(*parse_ctx_, ctx_);
        return this->out();
    }
};

class DynamicFormatter {
private:
    struct null_handler : fmt::internal::error_handler {
        void on_align(fmt::align_t) {}
        void on_plus() {}
        void on_minus() {}
        void on_space() {}
        void on_hash() {}
    };

public:
    template<typename ParseContext>
    auto parse(ParseContext& ctx) -> decltype(ctx.begin()) {
        format_str_ = ctx.begin();
        // Checks are deferred to formatting time when the argument type is known.
        fmt::internal::dynamic_specs_handler<ParseContext> handler(specs_, ctx);
        return parse_format_specs(ctx.begin(), ctx.end(), handler);
    }

    template<typename T, typename FormatContext>
    auto format(const T& val, FormatContext& ctx) -> decltype(ctx.out()) {
        handle_specs(ctx);
        fmt::internal::specs_checker<null_handler> checker(
            null_handler(), fmt::internal::mapped_type_constant<T, FormatContext>::value);
        checker.on_align(specs_.align);
        switch (specs_.sign) {
            case fmt::sign::none:
                break;
            case fmt::sign::plus:
                checker.on_plus();
                break;
            case fmt::sign::minus:
                checker.on_minus();
                break;
            case fmt::sign::space:
                checker.on_space();
                break;
        }
        if (specs_.alt)
            checker.on_hash();
        if (specs_.precision >= 0)
            checker.end_precision();

        using range = fmt::internal::output_range<typename FormatContext::iterator,
                                                  typename FormatContext::char_type>;
        fmt::visit_format_arg(ArgFormatter<range>(ctx, nullptr, &specs_),
                              fmt::internal::make_arg<FormatContext>(val));
        return ctx.out();
    }

private:
    template<typename Context>
    void handle_specs(Context& ctx) {
        fmt::internal::handle_dynamic_spec<fmt::internal::width_checker>(
            specs_.width, specs_.width_ref, ctx);
        fmt::internal::handle_dynamic_spec<fmt::internal::precision_checker>(
            specs_.precision, specs_.precision_ref, ctx);
    }

    fmt::internal::dynamic_format_specs<char> specs_;
    const char* format_str_;
};

} // namespace format::detail

template<>
struct fmt::formatter<slang::Type> {
    template<typename ParseContext>
    constexpr auto parse(ParseContext& ctx) {
        return ctx.begin();
    }

    template<typename FormatContext>
    auto format(const slang::Type& type, FormatContext& ctx) {
        bool unique = ctx.seenTypes.insert(&type).second;
        ctx.typeOptions->printAKA = unique;

        slang::TypePrinter printer;
        printer.setOptions(*ctx.typeOptions);
        printer.append(type);

        std::string result = printer.toString();
        return std::copy(result.begin(), result.end(), ctx.out());
    }
};

template<>
struct fmt::formatter<slang::ConstantValue> : format::detail::DynamicFormatter {
    template<typename FormatContext>
    auto format(const slang::ConstantValue& cv, FormatContext& ctx) {
        if (cv.isReal())
            return DynamicFormatter::format(double(cv.real()), ctx);
        if (cv.isShortReal())
            return DynamicFormatter::format(float(cv.real()), ctx);

        auto result = cv.toString();
        return std::copy(result.begin(), result.end(), ctx.out());
    }
};