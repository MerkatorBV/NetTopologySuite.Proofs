/* ============================================================================
   oracle/cpp/RocqNative.hpp
   ----------------------------------------------------------------------------
   Phase 5 reference binding: the C++ side of `libntsrocq` (oracle/nts_ffi.h).

   Header-only.  Loads the shared library at runtime (dlopen / LoadLibrary)
   so a consumer can ship without a link-time dependency.  Override the
   library path with NTS_ROCQ_LIB.  Default names: libntsrocq.so /
   libntsrocq.dylib / ntsrocq.dll.

   Threading: the embedded OCaml 4.14 runtime is not re-entrant.  Every
   call is serialised on a process-wide mutex.

   This file is the ABI twin of oracle/csharp/RocqNative.cs and
   oracle/java/.../RocqNative.java.  If they disagree, one of them is wrong.

   AI disclosure: authored with AI assistance (see CONTRIBUTING.md).
   ========================================================================== */

#ifndef NTS_ROCQ_NATIVE_HPP
#define NTS_ROCQ_NATIVE_HPP

#include <cstdint>
#include <cstdlib>
#include <mutex>
#include <stdexcept>
#include <string>
#include <utility>

#ifdef _WIN32
#ifndef WIN32_LEAN_AND_MEAN
#define WIN32_LEAN_AND_MEAN
#endif
#include <windows.h>
#else
#include <dlfcn.h>
#endif

namespace ntsrocq {

enum class OrientSign : int32_t {
    Neg = -1,
    Zero = 0,
    Pos = 1,
    Nan = 2,
    Uncertain = 3
};

enum class IntersectSign : int32_t {
    None = 0,
    Point = 1,
    Collinear = 2,
    Nan = 3,
    Uncertain = 4
};

enum class BooleanOp : int32_t {
    Union = 0,
    Intersection = 1,
    Difference = 2,
    SymDiff = 3
};

inline constexpr int32_t kExpectedAbiVersion = 1;

class RocqNative {
public:
    static bool isAvailable() {
        return instance().ok_;
    }

    static int32_t abiVersion() {
        return instance().require().abi_version_();
    }

    static OrientSign orientSignFiltered(
        double p0x, double p0y, double p1x, double p1y, double qx, double qy) {
        std::lock_guard<std::mutex> lock(instance().gate_);
        return static_cast<OrientSign>(
            instance().require().orient_sign_filtered_(p0x, p0y, p1x, p1y, qx, qy));
    }

    static OrientSign orientSignNaive(
        double p0x, double p0y, double p1x, double p1y, double qx, double qy) {
        std::lock_guard<std::mutex> lock(instance().gate_);
        return static_cast<OrientSign>(
            instance().require().orient_sign_naive_(p0x, p0y, p1x, p1y, qx, qy));
    }

    static OrientSign orientSignExact(
        double p0x, double p0y, double p1x, double p1y, double qx, double qy) {
        std::lock_guard<std::mutex> lock(instance().gate_);
        return static_cast<OrientSign>(
            instance().require().orient_sign_exact_(p0x, p0y, p1x, p1y, qx, qy));
    }

    static double orient2d(
        double p0x, double p0y, double p1x, double p1y, double qx, double qy) {
        std::lock_guard<std::mutex> lock(instance().gate_);
        return instance().require().orient2d_(p0x, p0y, p1x, p1y, qx, qy);
    }

    static IntersectSign intersectSignFiltered(
        double p0x, double p0y, double p1x, double p1y,
        double q0x, double q0y, double q1x, double q1y) {
        std::lock_guard<std::mutex> lock(instance().gate_);
        return static_cast<IntersectSign>(
            instance().require().intersect_sign_filtered_(
                p0x, p0y, p1x, p1y, q0x, q0y, q1x, q1y));
    }

    static bool tryIntersectPoint(
        double p0x, double p0y, double p1x, double p1y,
        double q0x, double q0y, double q1x, double q1y,
        double& x, double& y) {
        std::lock_guard<std::mutex> lock(instance().gate_);
        return instance().require().intersect_point_(
            p0x, p0y, p1x, p1y, q0x, q0y, q1x, q1y, &x, &y) == 1;
    }

    static bool passesThroughHotPixel(
        double p0x, double p0y, double p1x, double p1y, double cx, double cy) {
        std::lock_guard<std::mutex> lock(instance().gate_);
        return instance().require().passes_through_hot_pixel_(
            p0x, p0y, p1x, p1y, cx, cy) == 1;
    }

    static bool passesThroughHotPixelHalfOpen(
        double p0x, double p0y, double p1x, double p1y, double cx, double cy) {
        std::lock_guard<std::mutex> lock(instance().gate_);
        return instance().require().passes_through_hot_pixel_halfopen_(
            p0x, p0y, p1x, p1y, cx, cy) == 1;
    }

    static double snapCoord(double x) {
        std::lock_guard<std::mutex> lock(instance().gate_);
        return instance().require().snap_coord_(x);
    }

    static double snapCoordScaled(double x, double scale) {
        std::lock_guard<std::mutex> lock(instance().gate_);
        return instance().require().snap_coord_scaled_(x, scale);
    }

    static bool edgeInResult(BooleanOp op, bool inLeft, bool inRight) {
        std::lock_guard<std::mutex> lock(instance().gate_);
        int32_t r = instance().require().edge_in_result_(
            static_cast<int32_t>(op), inLeft ? 1 : 0, inRight ? 1 : 0);
        if (r < 0) {
            throw std::invalid_argument("nts_rocq_edge_in_result: unknown op");
        }
        return r == 1;
    }

    static double inCircle(
        double ax, double ay, double bx, double by,
        double cx, double cy, double px, double py) {
        std::lock_guard<std::mutex> lock(instance().gate_);
        return instance().require().in_circle_(ax, ay, bx, by, cx, cy, px, py);
    }

    static bool chordCrossesArcCircle(
        double sx, double sy, double mx, double my, double ex, double ey,
        double px, double py, double qx, double qy) {
        std::lock_guard<std::mutex> lock(instance().gate_);
        return instance().require().chord_crosses_arc_circle_(
            sx, sy, mx, my, ex, ey, px, py, qx, qy) == 1;
    }

    static bool arcPassesThroughHotPixel(
        double sx, double sy, double mx, double my, double ex, double ey,
        double cx, double cy, double scale) {
        std::lock_guard<std::mutex> lock(instance().gate_);
        return instance().require().arc_passes_through_hot_pixel_(
            sx, sy, mx, my, ex, ey, cx, cy, scale) == 1;
    }

    static std::pair<double, double> twoSum(double x, double y) {
        std::lock_guard<std::mutex> lock(instance().gate_);
        double sum = 0, err = 0;
        instance().require().two_sum_(x, y, &sum, &err);
        return {sum, err};
    }

private:
    using i32 = int32_t;
    using FnInit = i32 (*)();
    using FnAbi = i32 (*)();
    using FnOrient = i32 (*)(double, double, double, double, double, double);
    using FnOrient2d = double (*)(double, double, double, double, double, double);
    using FnIntersect = i32 (*)(double, double, double, double, double, double, double, double);
    using FnIntersectPt = i32 (*)(double, double, double, double, double, double, double, double, double*, double*);
    using FnPass = i32 (*)(double, double, double, double, double, double);
    using FnSnap = double (*)(double);
    using FnSnapScaled = double (*)(double, double);
    using FnEdge = i32 (*)(i32, i32, i32);
    using FnInCircle = double (*)(double, double, double, double, double, double, double, double);
    using FnChord = i32 (*)(double, double, double, double, double, double, double, double, double, double);
    using FnArcPix = i32 (*)(double, double, double, double, double, double, double, double, double);
    using FnTwoSum = void (*)(double, double, double*, double*);

    void* handle_ = nullptr;
    bool ok_ = false;
    std::mutex gate_;

    FnInit init_ = nullptr;
    FnAbi abi_version_ = nullptr;
    FnOrient orient_sign_filtered_ = nullptr;
    FnOrient orient_sign_naive_ = nullptr;
    FnOrient orient_sign_exact_ = nullptr;
    FnOrient2d orient2d_ = nullptr;
    FnIntersect intersect_sign_filtered_ = nullptr;
    FnIntersectPt intersect_point_ = nullptr;
    FnPass passes_through_hot_pixel_ = nullptr;
    FnPass passes_through_hot_pixel_halfopen_ = nullptr;
    FnSnap snap_coord_ = nullptr;
    FnSnapScaled snap_coord_scaled_ = nullptr;
    FnEdge edge_in_result_ = nullptr;
    FnInCircle in_circle_ = nullptr;
    FnChord chord_crosses_arc_circle_ = nullptr;
    FnArcPix arc_passes_through_hot_pixel_ = nullptr;
    FnTwoSum two_sum_ = nullptr;

    static RocqNative& instance() {
        static RocqNative n;
        return n;
    }

    RocqNative() {
        load();
    }

    RocqNative& require() {
        if (!ok_) {
            throw std::runtime_error(
                "libntsrocq is not available. Build it with `make -C oracle ffi` "
                "in NetTopologySuite.Proofs, or set NTS_ROCQ_LIB to the .so/.dylib/.dll.");
        }
        return *this;
    }

    template <typename T>
    T sym(const char* name) {
#ifdef _WIN32
        return reinterpret_cast<T>(GetProcAddress(static_cast<HMODULE>(handle_), name));
#else
        return reinterpret_cast<T>(dlsym(handle_, name));
#endif
    }

    static const char* defaultName() {
#ifdef _WIN32
        return "ntsrocq.dll";
#elif defined(__APPLE__)
        return "libntsrocq.dylib";
#else
        return "libntsrocq.so";
#endif
    }

    void load() {
        const char* override = std::getenv("NTS_ROCQ_LIB");
        const char* name = override && override[0] ? override : defaultName();
#ifdef _WIN32
        handle_ = static_cast<void*>(LoadLibraryA(name));
#else
        handle_ = dlopen(name, RTLD_NOW);
#endif
        if (!handle_) {
            return;
        }

        init_ = sym<FnInit>("nts_rocq_init");
        abi_version_ = sym<FnAbi>("nts_rocq_abi_version");
        orient_sign_filtered_ = sym<FnOrient>("nts_rocq_orient_sign_filtered");
        orient_sign_naive_ = sym<FnOrient>("nts_rocq_orient_sign_naive");
        orient_sign_exact_ = sym<FnOrient>("nts_rocq_orient_sign_exact");
        orient2d_ = sym<FnOrient2d>("nts_rocq_orient2d");
        intersect_sign_filtered_ = sym<FnIntersect>("nts_rocq_intersect_sign_filtered");
        intersect_point_ = sym<FnIntersectPt>("nts_rocq_intersect_point");
        passes_through_hot_pixel_ = sym<FnPass>("nts_rocq_passes_through_hot_pixel");
        passes_through_hot_pixel_halfopen_ = sym<FnPass>("nts_rocq_passes_through_hot_pixel_halfopen");
        snap_coord_ = sym<FnSnap>("nts_rocq_snap_coord");
        snap_coord_scaled_ = sym<FnSnapScaled>("nts_rocq_snap_coord_scaled");
        edge_in_result_ = sym<FnEdge>("nts_rocq_edge_in_result");
        in_circle_ = sym<FnInCircle>("nts_rocq_in_circle");
        chord_crosses_arc_circle_ = sym<FnChord>("nts_rocq_chord_crosses_arc_circle");
        arc_passes_through_hot_pixel_ = sym<FnArcPix>("nts_rocq_arc_passes_through_hot_pixel");
        two_sum_ = sym<FnTwoSum>("nts_rocq_two_sum");

        if (!init_ || !abi_version_ || !orient_sign_filtered_ || !orient_sign_exact_
            || !in_circle_) {
            return;
        }
        if (init_() != 0) {
            return;
        }
        if (abi_version_() != kExpectedAbiVersion) {
            return;
        }
        ok_ = true;
    }
};

} // namespace ntsrocq

#endif /* NTS_ROCQ_NATIVE_HPP */
