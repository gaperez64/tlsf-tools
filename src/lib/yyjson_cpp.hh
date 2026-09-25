#pragma once

#include <yyjson.h>

#include <charconv>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <memory>
#include <stdexcept>
#include <string>
#include <string_view>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

// Small C++ value facade for the yyjson reader and mutable writer.  The JSON
// parsing and escaping are performed by yyjson; this facade only owns values.
namespace tlsf_json {
struct object;
struct array;

struct value {
  using data_type =
      std::variant<std::nullptr_t, bool, int64_t, uint64_t, double, std::string,
                   std::shared_ptr<object>, std::shared_ptr<array>>;
  data_type data = nullptr;

  value() = default;
  value(std::nullptr_t) {}
  value(bool v) : data(v) {}
  template <typename T, typename = std::enable_if_t<std::is_integral_v<T> &&
                                                    !std::is_same_v<T, bool>>>
  value(T v)
      : data(std::is_signed_v<T> ? data_type(int64_t(v))
                                 : data_type(uint64_t(v))) {}
  value(double v) : data(v) {}
  value(const char *v) : data(std::string(v)) {}
  value(const std::string &v) : data(v) {}
  value(std::string_view v) : data(std::string(v)) {}
  value(const object &v);
  value(object &&v);
  value(const array &v);
  value(array &&v);
  value(const value &other);
  value(value &&) noexcept = default;
  value &operator=(const value &other);
  value &operator=(value &&) noexcept = default;

  bool is_null() const { return std::holds_alternative<std::nullptr_t>(data); }
  bool is_object() const {
    return std::holds_alternative<std::shared_ptr<object>>(data);
  }
  bool is_array() const {
    return std::holds_alternative<std::shared_ptr<array>>(data);
  }
  bool is_int64() const { return std::holds_alternative<int64_t>(data); }
  int64_t as_int64() const { return std::get<int64_t>(data); }
  uint64_t as_uint64() const { return std::get<uint64_t>(data); }
  bool as_bool() const { return std::get<bool>(data); }
  std::string_view as_string() const { return std::get<std::string>(data); }
  object &as_object() { return *std::get<std::shared_ptr<object>>(data); }
  const object &as_object() const {
    return *std::get<std::shared_ptr<object>>(data);
  }
  array &as_array() { return *std::get<std::shared_ptr<array>>(data); }
  const array &as_array() const {
    return *std::get<std::shared_ptr<array>>(data);
  }
};

struct object : std::vector<std::pair<std::string, value>> {
  using base = std::vector<std::pair<std::string, value>>;
  object() = default;
  object(std::initializer_list<base::value_type> init) : base(init) {}
  value *if_contains(std::string_view key) {
    for (auto &item : *this)
      if (item.first == key)
        return &item.second;
    return nullptr;
  }
  const value *if_contains(std::string_view key) const {
    return const_cast<object *>(this)->if_contains(key);
  }
  bool contains(std::string_view key) const {
    return if_contains(key) != nullptr;
  }
  value &at(std::string_view key) {
    if (auto *found = if_contains(key))
      return *found;
    throw std::out_of_range("JSON key missing: " + std::string(key));
  }
  const value &at(std::string_view key) const {
    return const_cast<object *>(this)->at(key);
  }
  value &operator[](std::string_view key) {
    if (auto *found = if_contains(key))
      return *found;
    emplace_back(std::string(key), value());
    return back().second;
  }
};

struct array : std::vector<value> {
  using std::vector<value>::vector;
};

inline value::value(const object &v) : data(std::make_shared<object>(v)) {}
inline value::value(object &&v)
    : data(std::make_shared<object>(std::move(v))) {}
inline value::value(const array &v) : data(std::make_shared<array>(v)) {}
inline value::value(array &&v) : data(std::make_shared<array>(std::move(v))) {}
inline value::value(const value &other) : data(other.data) {
  if (other.is_object())
    data = std::make_shared<object>(other.as_object());
  else if (std::holds_alternative<std::shared_ptr<array>>(other.data))
    data = std::make_shared<array>(other.as_array());
}
inline value &value::operator=(const value &other) {
  if (this != &other)
    *this = value(other);
  return *this;
}

inline value decode(yyjson_val *raw) {
  if (yyjson_is_null(raw))
    return nullptr;
  if (yyjson_is_bool(raw))
    return yyjson_get_bool(raw);
  if (yyjson_is_sint(raw))
    return yyjson_get_sint(raw);
  if (yyjson_is_uint(raw)) {
    uint64_t number = yyjson_get_uint(raw);
    return number <= INT64_MAX ? value(int64_t(number)) : value(number);
  }
  if (yyjson_is_real(raw))
    return yyjson_get_real(raw);
  if (yyjson_is_str(raw))
    return std::string_view(yyjson_get_str(raw), yyjson_get_len(raw));
  if (yyjson_is_arr(raw)) {
    array out;
    size_t idx, max;
    yyjson_val *item;
    yyjson_arr_foreach(raw, idx, max, item) out.push_back(decode(item));
    return out;
  }
  if (yyjson_is_obj(raw)) {
    object out;
    size_t idx, max;
    yyjson_val *key, *item;
    yyjson_obj_foreach(raw, idx, max, key, item) {
      std::string_view name(yyjson_get_str(key), yyjson_get_len(key));
      if (out.contains(name))
        throw std::runtime_error("duplicate JSON key");
      out.emplace_back(std::string(name), decode(item));
    }
    return out;
  }
  throw std::runtime_error("invalid JSON value");
}

inline value parse(std::string_view text) {
  yyjson_read_err err{};
  yyjson_doc *doc = yyjson_read_opts(const_cast<char *>(text.data()),
                                     text.size(), 0, nullptr, &err);
  if (!doc)
    throw std::runtime_error(err.msg ? err.msg : "invalid JSON");
  try {
    value out = decode(yyjson_doc_get_root(doc));
    yyjson_doc_free(doc);
    return out;
  } catch (...) {
    yyjson_doc_free(doc);
    throw;
  }
}

inline yyjson_mut_val *encode(yyjson_mut_doc *doc, const value &v) {
  yyjson_mut_val *raw = nullptr;
  if (v.is_null())
    raw = yyjson_mut_null(doc);
  else if (auto p = std::get_if<bool>(&v.data))
    raw = yyjson_mut_bool(doc, *p);
  else if (auto p = std::get_if<int64_t>(&v.data))
    raw = yyjson_mut_sint(doc, *p);
  else if (auto p = std::get_if<uint64_t>(&v.data))
    raw = yyjson_mut_uint(doc, *p);
  else if (auto p = std::get_if<double>(&v.data)) {
    if (!std::isfinite(*p))
      throw std::runtime_error("non-finite JSON number");
    char buffer[128];
    auto [end, error] = std::to_chars(buffer, buffer + sizeof buffer, *p,
                                      std::chars_format::scientific);
    if (error != std::errc{})
      throw std::runtime_error("cannot format JSON number");
    std::string number(buffer, end);
    size_t exponent = number.find('e');
    number = number.substr(0, exponent) + "E" +
             std::to_string(std::stoi(number.substr(exponent + 1)));
    raw = yyjson_mut_rawcpy(doc, number.c_str());
  } else if (auto p = std::get_if<std::string>(&v.data))
    raw = yyjson_mut_strncpy(doc, p->data(), p->size());
  else if (v.is_object()) {
    raw = yyjson_mut_obj(doc);
    if (!raw)
      throw std::bad_alloc();
    for (const auto &[key, item] : v.as_object()) {
      auto *name = yyjson_mut_strncpy(doc, key.data(), key.size());
      auto *child = encode(doc, item);
      if (!name || !yyjson_mut_obj_add(raw, name, child))
        throw std::bad_alloc();
    }
  } else {
    raw = yyjson_mut_arr(doc);
    if (!raw)
      throw std::bad_alloc();
    for (const auto &item : v.as_array())
      if (!yyjson_mut_arr_append(raw, encode(doc, item)))
        throw std::bad_alloc();
  }
  if (!raw)
    throw std::bad_alloc();
  return raw;
}

inline std::string serialize(const value &v) {
  yyjson_mut_doc *doc = yyjson_mut_doc_new(nullptr);
  if (!doc)
    throw std::bad_alloc();
  try {
    yyjson_mut_doc_set_root(doc, encode(doc, v));
    size_t size = 0;
    char *bytes = yyjson_mut_write(doc, 0, &size);
    if (!bytes)
      throw std::bad_alloc();
    std::unique_ptr<char, decltype(&free)> owned_bytes(bytes, &free);
    std::string out(owned_bytes.get(), size);
    yyjson_mut_doc_free(doc);
    return out;
  } catch (...) {
    yyjson_mut_doc_free(doc);
    throw;
  }
}

inline bool operator==(const value &lhs, std::string_view rhs) {
  return std::holds_alternative<std::string>(lhs.data) &&
         lhs.as_string() == rhs;
}
inline bool operator==(const value &lhs, const char *rhs) {
  return lhs == std::string_view(rhs);
}
inline bool operator==(const value &lhs, bool rhs) {
  return std::holds_alternative<bool>(lhs.data) && lhs.as_bool() == rhs;
}
} // namespace tlsf_json
