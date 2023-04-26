#pragma once

namespace netlist {

class Config {
private:

public:
  bool debugEnabled;

  Config() : debugEnabled(false) {};

  static Config &getInstance() {
    static Config instance;
    return instance;
  }

  // Prevent copies from being made.
  Config(Config const&) = delete;
  void operator=(Config const&) = delete;
};

} // End namespace netlist.
