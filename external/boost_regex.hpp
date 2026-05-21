// SPDX-FileCopyrightText: Michael Popoloski
// SPDX-License-Identifier: MIT
//
// When used in "standalone" mode, boost::regex doesn't detect whether exceptions
// are enabled, so manully do that here. It sure seems like this should just be
// done in the lib itself but oh well.

#if !defined(__cpp_exceptions) || __cpp_exceptions == 0
#    define BOOST_NO_EXCEPTIONS
#endif
#include <boost/regex.hpp>
