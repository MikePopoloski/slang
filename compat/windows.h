// This is a compatibility header that includes only the few pieces of
// Windows.h that we actually need. The rest of it has tons of annoying
// macros that cause problems when compiled with the rest of the code.
#pragma once

#include <cstdarg>

typedef char CHAR;
typedef wchar_t WCHAR;
typedef int BOOL;
typedef unsigned int UINT;
typedef unsigned short WORD;
typedef unsigned long DWORD;
typedef __int64 LONG_PTR, *PLONG_PTR;
typedef unsigned __int64 ULONG_PTR, *PULONG_PTR;
typedef ULONG_PTR DWORD_PTR, *PDWORD_PTR;
typedef void *HANDLE;
typedef WCHAR *NWPSTR, *LPWSTR, *PWSTR;
typedef const WCHAR *LPCWSTR, *PCWSTR;
typedef const WCHAR *LPCWCH, *PCWCH;
typedef const CHAR *LPCSTR, *PCSTR;
typedef const CHAR *LPCCH, *PCCH;
typedef CHAR *NPSTR, *LPSTR, *PSTR;
typedef BOOL *LPBOOL;
typedef void *LPVOID;
typedef const void *LPCVOID;
typedef DWORD *LPDWORD;

#define WINAPI __stdcall
#define NO_ERROR 0L
#define ERROR_SUCCESS 0L
#define ERROR_NO_MORE_FILES 18L
#define ERROR_INVALID_PARAMETER 87L
#define ERROR_INSUFFICIENT_BUFFER 122L
#define MAX_PATH 260
#define CP_UTF8 65001
#define MB_ERR_INVALID_CHARS 0x00000008
#define LANG_NEUTRAL 0x00
#define SUBLANG_DEFAULT 0x01
#define INVALID_FILE_SIZE ((DWORD)0xFFFFFFFF)
#define INVALID_FILE_ATTRIBUTES ((DWORD)-1)
#define INVALID_HANDLE_VALUE ((HANDLE)(LONG_PTR)-1)
#define FILE_ATTRIBUTE_DIRECTORY 0x00000010

#define FORMAT_MESSAGE_IGNORE_INSERTS  0x00000200
#define FORMAT_MESSAGE_FROM_STRING     0x00000400
#define FORMAT_MESSAGE_FROM_HMODULE    0x00000800
#define FORMAT_MESSAGE_FROM_SYSTEM     0x00001000
#define FORMAT_MESSAGE_ARGUMENT_ARRAY  0x00002000
#define FORMAT_MESSAGE_MAX_WIDTH_MASK  0x000000FF

#define DECLARE_HANDLE(name) struct name##__{int unused;}; typedef struct name##__ *name
#define MAKELANGID(p, s) ((((WORD  )(s)) << 10) | (WORD  )(p))

DECLARE_HANDLE(HWND);

extern "C" {
    typedef struct _FILETIME {
        DWORD dwLowDateTime;
        DWORD dwHighDateTime;
    } FILETIME, *PFILETIME, *LPFILETIME;

    typedef struct _WIN32_FIND_DATAW {
        DWORD dwFileAttributes;
        FILETIME ftCreationTime;
        FILETIME ftLastAccessTime;
        FILETIME ftLastWriteTime;
        DWORD nFileSizeHigh;
        DWORD nFileSizeLow;
        DWORD dwReserved0;
        DWORD dwReserved1;
        WCHAR  cFileName[MAX_PATH];
        WCHAR  cAlternateFileName[14];
    } WIN32_FIND_DATAW, *PWIN32_FIND_DATAW, *LPWIN32_FIND_DATAW;

    typedef struct _SYSTEM_INFO {
        union {
            DWORD dwOemId;          // Obsolete field...do not use
            struct {
                WORD wProcessorArchitecture;
                WORD wReserved;
            } DUMMYSTRUCTNAME;
        } DUMMYUNIONNAME;
        DWORD dwPageSize;
        LPVOID lpMinimumApplicationAddress;
        LPVOID lpMaximumApplicationAddress;
        DWORD_PTR dwActiveProcessorMask;
        DWORD dwNumberOfProcessors;
        DWORD dwProcessorType;
        DWORD dwAllocationGranularity;
        WORD wProcessorLevel;
        WORD wProcessorRevision;
    } SYSTEM_INFO, *LPSYSTEM_INFO;

    DWORD WINAPI GetFileAttributesW(LPCWSTR lpFileName);
    DWORD WINAPI GetFullPathNameW(LPCWSTR lpFileName, DWORD nBufferLength, LPWSTR lpBuffer, LPWSTR * lpFilePart);
    DWORD WINAPI GetFileSize(HANDLE hFile, LPDWORD lpFileSizeHigh);
    HANDLE WINAPI FindFirstFileW(LPCWSTR lpFileName, LPWIN32_FIND_DATAW lpFindFileData);
    BOOL WINAPI FindNextFileW(HANDLE hFindFile, LPWIN32_FIND_DATAW lpFindFileData);
    BOOL WINAPI FindClose(HANDLE hFindFile);
    DWORD WINAPI GetLastError(void);
    HWND WINAPI GetConsoleWindow(void);
    BOOL WINAPI AllocConsole(void);
    HWND WINAPI SetFocus(HWND hWnd);
    void WINAPI OutputDebugStringA(LPCSTR lpOutputString);
    void WINAPI GetSystemInfo(LPSYSTEM_INFO lpSystemInfo);

    DWORD WINAPI FormatMessageW(DWORD dwFlags, LPCVOID lpSource, DWORD dwMessageId, DWORD dwLanguageId,
                                LPWSTR lpBuffer, DWORD nSize, va_list *Arguments);

    int WINAPI MultiByteToWideChar(UINT CodePage, DWORD dwFlags, LPCCH lpMultiByteStr,
                                   int cbMultiByte, LPWSTR lpWideCharStr, int cchWideChar);

    int WINAPI WideCharToMultiByte(UINT CodePage, DWORD dwFlags, LPCWCH lpWideCharStr,
                                   int cchWideChar, LPSTR lpMultiByteStr, int cbMultiByte,
                                   LPCCH lpDefaultChar, LPBOOL lpUsedDefaultChar);
}