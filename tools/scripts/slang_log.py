#!/usr/bin/env python3

import re
import argparse
from collections import defaultdict
errors = 0
warnings = 0

def parse_log_file(file_path):
    global errors, warnings
    with open(file_path, 'r') as file:
        lines = file.readlines()

    log_entries = []
    i = 0
    j = 0
    entry = []
    # error messages may start with one or more prefix linex: '^in file included from ' or '^  in instance:'
    # optionally followed by 1 or more  3 line or 1 line notes
    # followed by a 3-line error/warning message
    # optionally followed by 1 or more  3 line or 1 line notes
    finalize = False # if encountering a prefix we can save the last error and start a new one
    prefix = False # set when encountered first prefix cleared when getting actual error/warning
    while j < len(lines):
        if re.match(r'^  in instance:', lines[j]) or re.match(r'^in file included from ', lines[j]):
            if entry and not prefix:
                log_entries.append(entry)
                entry = []
                i = j
            if not prefix:
                j = i + 1
                entry = lines[i:j]
            else:
                # append to existing prefix
                entry.append(lines[j])
                j = j + 1
            finalize = False # no wrror/warning yet
            prefix = True # we're started a prefix, dont clear entry on next prefix
        elif re.match(r'.*:(\d+):(\d+): (error|warning): .*', lines[j]):
            if finalize:
                log_entries.append(entry)
                entry = []
                i = j
            j = j + 3
            entry = lines[i:j]
            prefix = False
            finalize = True
        elif re.match(r'^note: from', lines[j]):
            entry.extend(lines[j:j+1])
            j += 1
        elif re.match(r'.*:(\d+):(\d+): note: .*', lines[j]):
            entry.extend(lines[j:j+3])
            j += 3
        else:
            if m := re.match(r'^Build.*: (\d+) errors, (\d+) warnings', lines[-1]):
                errors = m.group(1)
                warnings = m.group(2)
            if entry:
                log_entries.append(entry)
            break
    return log_entries

def error_warning_line(entry):
    for en in entry:
        if re.match(r'.*:(\d+):(\d+): (error|warning): .*', en):
            return en

def filter_entries(entries, include=None, exclude=None, include_file=None, exclude_file=None):
    filtered_entries = []
    for entry in entries:
        e = error_warning_line(entry)
        filename = e.split(':')[0]
        message = e.split(':', 3)[-1].strip()

        
        if include and not any(re.search(pattern, message) for pattern in include):
            continue
        if exclude and any(re.search(pattern, message) for pattern in exclude):
            continue
        if include_file and not any(re.search(pattern, filename) for pattern in include_file):
            continue
        if exclude_file and any(re.search(pattern, filename) for pattern in exclude_file):
            continue
        
        filtered_entries.append(entry)
    return filtered_entries

def summarize_entries(entries):
    summary = defaultdict(int)
    for entry in entries:
        e = error_warning_line(entry)
        message = re.sub(r'\'[^\']*\'', '<something>', e.split(':', 3)[-1].strip())
        summary[message] += 1
    return summary

def main():
    global errors, warnings
    parser = argparse.ArgumentParser(description='Log Analyzer')
    parser.add_argument('logfile', help='Path to the log file')
    parser.add_argument('-s', '--summary', action='store_true', help='List number of errors and warnings of each kind')
    parser.add_argument('-x', '--exclude', action='append', help='Exclude messages matching the regexp')
    parser.add_argument('-i', '--include', action='append', help='Include only messages matching the regexp')
    parser.add_argument('-X', '--exclude-file', action='append', help='Ignore messages whose filename matches the regexp')
    parser.add_argument('-I', '--include-file', action='append', help='Include only messages whose filename matches the regexp')

    args = parser.parse_args()

    if args.include and args.exclude:
        parser.error("--include and --exclude cannot be mixed")
    if args.include_file and args.exclude_file:
        parser.error("--include-file and --exclude-file cannot be mixed")

    log_entries = parse_log_file(args.logfile)
    filtered_entries = filter_entries(log_entries, args.include, args.exclude, args.include_file, args.exclude_file)

    if args.summary:
        total = {}
        summary = summarize_entries(filtered_entries)
        for message, count in sorted(summary.items()):
            print(f"{message}: {count}")
            t = message.split(':')[0]
            if t in total:
                total[t] += count
            else:
                total[t] = count
        if int(errors) != total['error'] or int(warnings) != total['warning']:
            print(f"Mismatch! Errors: log={errors},counted={total['error']}, Warnings:log={warnings},counted={total['warning']}")
        else:
            print(f"Errors: {errors}, Warnings:{warnings}")
    else:
        for entry in filtered_entries:
            for line in entry:
                print(line, end='')

if __name__ == "__main__":
    main()