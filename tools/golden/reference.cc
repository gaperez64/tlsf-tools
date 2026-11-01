// Tools-only oracle: REQUIRES Spot 2.16. Never built or run by Meson/CI.
// reference FORMULA AP1,AP2,... WORDS; WORDS lines are prefix-masks;loop-masks.
#include <spot/tl/parse.hh>
#include <spot/twaalgos/translate.hh>
#include <spot/twaalgos/word.hh>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>

static std::string tree(spot::formula f) {
  using spot::op;
  switch (f.kind()) {
  case op::tt:
    return "1";
  case op::ff:
    return "0";
  case op::ap:
    return "$" + f.ap_name();
  default:
    break;
  }
  std::string token;
  switch (f.kind()) {
  case op::Not:
    token = "!";
    break;
  case op::X:
    token = "X";
    break;
  case op::F:
    token = "F";
    break;
  case op::G:
    token = "G";
    break;
  case op::U:
    token = "U";
    break;
  case op::R:
    token = "R";
    break;
  case op::W:
    token = "W";
    break;
  case op::M:
    token = "M";
    break;
  case op::Implies:
    token = "i";
    break;
  case op::Equiv:
    token = "e";
    break;
  case op::Xor:
    token = "^";
    break;
  case op::And:
    token = "&";
    break;
  case op::Or:
    token = "|";
    break;
  default:
    throw std::runtime_error("unsupported formula");
  }
  std::string result = tree(f[0]);
  if (f.size() == 1)
    return token + " " + result;
  for (unsigned i = 1; i < f.size(); ++i)
    result = token + " " + result + " " + tree(f[i]);
  return result;
}

int main(int argc, char **argv) {
  if (argc != 4 && argc != 5)
    return 2;
  auto parsed = spot::parse_infix_psl(argv[1]);
  if (parsed.format_errors(std::cerr))
    return 2;
  std::cout << tree(parsed.f) << '\n';
  if (argc == 5 && std::string(argv[4]) == "--tree-only")
    return 0;
  spot::translator translate;
  auto aut = translate.run(parsed.f);
  std::vector<std::string> names;
  std::istringstream ap(argv[2]);
  std::string name;
  while (std::getline(ap, name, ','))
    names.push_back(name);
  auto letters = [&](std::string masks) {
    std::istringstream input(masks);
    std::string mask, result;
    while (input >> mask) {
      auto value = std::stoull(mask);
      if (!result.empty())
        result += ';';
      std::string letter;
      for (size_t i = 0; i < names.size(); ++i) {
        if (!letter.empty())
          letter += " & ";
        letter += (value & (1ULL << i) ? "" : "!") + std::string("\"") +
                  names[i] + "\"";
      }
      result += letter.empty() ? "1" : letter;
    }
    return result;
  };
  std::ifstream words(argv[3]);
  std::string line;
  while (std::getline(words, line)) {
    auto separator = line.find(';');
    auto prefix = letters(line.substr(0, separator));
    auto loop = letters(line.substr(separator + 1));
    if (!prefix.empty())
      prefix += ';';
    auto word =
        spot::parse_word(prefix + "cycle{" + loop + "}", aut->get_dict());
    std::cout << (word->intersects(aut) ? '1' : '0');
  }
  std::cout << '\n';
}
