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
class BasicFormatContext
    : public fmt::internal::context_base<OutputIt, BasicFormatContext<OutputIt>, char> {
public:
    using char_type = char;

    template<typename T>
    struct formatter_type {
        using type = fmt::formatter<T, char_type>;
    };

private:
    fmt::internal::arg_map<BasicFormatContext> map_;

    BasicFormatContext(const BasicFormatContext&) = delete;
    void operator=(const BasicFormatContext&) = delete;

    using base = fmt::internal::context_base<OutputIt, BasicFormatContext, char_type>;
    using format_arg = typename base::format_arg;
    using base::get_arg;

public:
    using typename base::iterator;

    BasicFormatContext(OutputIt out, fmt::basic_string_view<char_type> format_str,
                       fmt::basic_format_args<BasicFormatContext> ctx_args,
                       fmt::internal::locale_ref loc = fmt::internal::locale_ref()) :
        base(out, format_str, ctx_args, loc) {}

    format_arg next_arg() { return this->do_get_arg(this->parse_context().next_arg_id()); }
    format_arg get_arg(unsigned arg_id) { return this->do_get_arg(arg_id); }

    format_arg get_arg(fmt::basic_string_view<char_type>) { return format_arg(); }

    TypePrintingOptions* typeOptions;
    flat_hash_set<const Type*> seenTypes;
};

using FormatContext =
    BasicFormatContext<std::back_insert_iterator<fmt::internal::basic_buffer<char>>>;

template<typename Range>
class ArgFormatter
    : public fmt::internal::function<typename fmt::internal::arg_formatter_base<Range>::iterator>,
      public fmt::internal::arg_formatter_base<Range> {
private:
    using char_type = typename Range::value_type;
    using base = fmt::internal::arg_formatter_base<Range>;
    using context_type = BasicFormatContext<typename base::iterator>;

    context_type& ctx_;

public:
    using range = Range;
    using iterator = typename base::iterator;
    using format_specs = typename base::format_specs;

    explicit ArgFormatter(context_type& ctx, format_specs* spec = FMT_NULL) :
        base(Range(ctx.out()), spec, ctx.locale()), ctx_(ctx) {}

    using base::operator();

    iterator operator()(typename fmt::basic_format_arg<context_type>::handle handle) {
        handle.format(ctx_);
        return this->out();
    }
};

class DynamicFormatter {
private:
    struct null_handler : fmt::internal::error_handler {
        void on_align(fmt::alignment) {}
        void on_plus() {}
        void on_minus() {}
        void on_space() {}
        void on_hash() {}
    };

public:
    template<typename ParseContext>
    auto parse(ParseContext& ctx) -> decltype(ctx.begin()) {
        // Checks are deferred to formatting time when the argument type is known.
        fmt::internal::dynamic_specs_handler<ParseContext> handler(specs_, ctx);
        return parse_format_specs(ctx.begin(), ctx.end(), handler);
    }

    template<typename T, typename FormatContext>
    auto format(const T& val, FormatContext& ctx) -> decltype(ctx.out()) {
        handle_specs(ctx);
        fmt::internal::specs_checker<null_handler> checker(
            null_handler(), fmt::internal::get_type<FormatContext, T>::value);
        checker.on_align(specs_.align());
        if (specs_.flags == 0)
            ; // Do nothing.
        else if (specs_.has(fmt::SIGN_FLAG))
            specs_.has(fmt::PLUS_FLAG) ? checker.on_plus() : checker.on_space();
        else if (specs_.has(fmt::MINUS_FLAG))
            checker.on_minus();
        else if (specs_.has(fmt::HASH_FLAG))
            checker.on_hash();

        if (specs_.precision != -1)
            checker.end_precision();

        using range =
            fmt::output_range<typename FormatContext::iterator, typename FormatContext::char_type>;
        fmt::visit_format_arg(ArgFormatter<range>(ctx, &specs_),
                              fmt::internal::make_arg<FormatContext>(val));
        return ctx.out();
    }

private:
    template<typename Context>
    void handle_specs(Context& ctx) {
        fmt::internal::handle_dynamic_spec<fmt::internal::width_checker>(specs_.width_,
                                                                         specs_.width_ref, ctx);
        fmt::internal::handle_dynamic_spec<fmt::internal::precision_checker>(
            specs_.precision, specs_.precision_ref, ctx);
    }

    fmt::internal::dynamic_format_specs<char> specs_;
};

} // namespace

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