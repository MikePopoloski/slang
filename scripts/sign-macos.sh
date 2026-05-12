#!/usr/bin/env bash
set -euo pipefail

# Import the Developer ID signing certificate into a temporary keychain.
KEYCHAIN_PATH="$RUNNER_TEMP/build.keychain-db"
KEYCHAIN_PASSWORD="$(openssl rand -base64 24)"
CERT_PATH="$RUNNER_TEMP/certificate.p12"

echo -n "$MACOS_CERTIFICATE" | base64 --decode -o "$CERT_PATH"

security create-keychain -p "$KEYCHAIN_PASSWORD" "$KEYCHAIN_PATH"
security set-keychain-settings -lut 21600 "$KEYCHAIN_PATH"
security unlock-keychain -p "$KEYCHAIN_PASSWORD" "$KEYCHAIN_PATH"
security import "$CERT_PATH" -P "$MACOS_CERTIFICATE_PASSWORD" -A -t cert -f pkcs12 -k "$KEYCHAIN_PATH"
security set-key-partition-list -S apple-tool:,apple:,codesign: -s -k "$KEYCHAIN_PASSWORD" "$KEYCHAIN_PATH"
security list-keychains -d user -s "$KEYCHAIN_PATH" $(security list-keychains -d user | tr -d '"')

# Sign with hardened runtime and a secure timestamp.
BIN_PATH="build/bin/slang"
codesign --force --options runtime --timestamp --sign "$MACOS_SIGNING_IDENTITY" "$BIN_PATH"
codesign --verify --strict --verbose=2 "$BIN_PATH"

# Notarize using an App Store Connect API key. Standalone Mach-O
# binaries cannot be stapled, but notarization is still recorded by
# Apple's online check.
API_KEY_PATH="$RUNNER_TEMP/AuthKey.p8"
echo -n "$MACOS_NOTARIZATION_API_KEY" | base64 --decode -o "$API_KEY_PATH"

ZIP_PATH="$RUNNER_TEMP/slang-notarize.zip"
ditto -c -k --keepParent "$BIN_PATH" "$ZIP_PATH"
xcrun notarytool submit "$ZIP_PATH" --key "$API_KEY_PATH" --key-id "$MACOS_NOTARIZATION_API_KEY_ID" --issuer "$MACOS_NOTARIZATION_API_ISSUER_ID"

# Clean up the keychain and secrets so they aren't left on the runner.
security delete-keychain "$KEYCHAIN_PATH"
rm -f "$CERT_PATH" "$API_KEY_PATH"
