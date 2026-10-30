"""
ĐIỂM TIN & LẮNG NGHE DƯ LUẬN — SCRIPT QUÉT TIN (chạy định kỳ trên GitHub Actions)

Mỗi lần chạy:
  1. Quét RSS cho 5 mục: Tiêu điểm 24h, Quốc tế, Dư luận MXH, Địa phương, Tuyên giáo TW
     (giữ nguyên cách lọc của bản Streamlit v5.7: chặn nguồn xấu, lọc đúng 124 xã/phường...).
  2. Ghi danh sách tin vào bảng Supabase `dt_bai`.
  3. Với tin mới: giải mã link Google News ra link báo gốc, tải bài và bóc nội dung
     (chế độ đọc) để trang web hiện ngay khi bấm vào tin.
  4. Rà lại tin 7 ngày gần nhất: chấm lại sắc thái, ẩn tin ngoài tỉnh lọt vào trước đó.
  5. Xóa tin cũ hơn 30 ngày cho nhẹ cơ sở dữ liệu.

Biến môi trường cần có (đặt trong GitHub > Settings > Secrets and variables > Actions):
  SUPABASE_URL          vd: https://elkysoeukqtweytkekwr.supabase.co
  SUPABASE_SERVICE_KEY  khóa service_role (KHÔNG phải anon key, KHÔNG đưa vào index.html)

Thử bộ chấm sắc thái trên máy (không cần Supabase):
  python crawler/quet_tin.py --thu "Tiêu đề tin" "Tóm tắt (sapo) nếu có"
Thử bộ lọc địa bàn:
  python crawler/quet_tin.py --thu-dia-ban "Tiêu đề tin" "Tên nguồn"
"""

import base64
import calendar
import datetime as dt
import hashlib
import json
import os
import re
import sys
import threading
import time
import unicodedata
from concurrent.futures import ThreadPoolExecutor, as_completed
from urllib.parse import quote

import feedparser
import requests
import trafilatura

# =====================================================================
# CẤU HÌNH
# =====================================================================
SUPABASE_URL = os.environ.get("SUPABASE_URL", "").rstrip("/")
SUPABASE_KEY = os.environ.get("SUPABASE_SERVICE_KEY", "")

PHIEN_BAN = "2026-10-30"   # in ra log GitHub Actions để biết đang chạy bản nào

SO_NGAY_LUU = 30          # xóa tin cũ hơn số ngày này
SO_NGAY_CHAM_LAI = 7      # chấm lại sắc thái cho tin trong bấy nhiêu ngày gần nhất
MAX_TRICH_XUAT = 150      # số bài tối đa bóc nội dung mỗi lần chạy
SO_LAN_THU_TOI_DA = 3     # bài bóc lỗi sẽ thử lại tối đa bấy nhiêu lần
SO_LUONG = 4              # số luồng tải bài song song

UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
      "(KHTML, like Gecko) Chrome/129.0 Safari/537.36")

BLACKLIST = ["bbc", "rfa", "voa", "rfi", "việt tân", "viet tan", "luatkhoa", "thoibao", "nguoi-viet"]

LOCAL_KEYWORDS = [
    "tuyên quang", "hàm yên", "sơn dương", "chiêm hóa", "nà hang", "na hang", "lâm bình", "yên sơn",
    "hà giang 2", "tân trịnh", "thái hòa", "sơn thủy", "tát ngà", "an tường", "bắc mê", "bắc quang",
    "bạch đích", "bạch ngọc", "bạch xa", "bản máy", "bằng hành", "bằng lang", "bình an", "bình ca",
    "bình thuận", "bình xa", "cán tỷ", "cao bồ", "côn lôn", "đồng tâm", "đông thọ", "đồng văn",
    "đồng yên", "du già", "đường hồng", "đường thượng", "giáp trung", "hà giang 1", "hồ thầu",
    "hoàng su phì", "hồng sơn", "hồng thái", "hùng an", "hùng đức", "hùng lợi", "khâu vai",
    "khuôn lùng", "kiên đài", "kiến thiết", "hòa an", "kim bình", "lao chải", "liên hiệp", "linh hồ",
    "lực hành", "lũng cú", "lũng phìn", "lùng tám", "mậu duệ", "mèo vạc", "minh ngọc", "minh quang",
    "minh sơn", "minh tân", "minh thanh", "minh xuân", "mỹ lâm", "nấm dẩn", "nậm dịch", "nghĩa thuận",
    "ngọc đường", "ngọc long", "nhữ khê", "niêm sơn", "nông tiến", "pà vầy sủ", "phố bảng", "phú linh",
    "phú lương", "phù lưu", "pờ ly ngài", "quản bạ", "quang bình", "quảng nguyên", "sà phìn",
    "tùng bá", "sơn vĩ", "sủng máng", "tân an", "tân long", "tân mỹ", "tân quang", "tân thanh",
    "tân tiến", "tân trào", "thái bình", "thuận hòa", "thái sơn", "thắng mố", "thàng tín",
    "thanh thủy", "thông nguyên", "thượng lâm", "thượng nông", "thượng sơn", "tiên nguyên",
    "tiên yên", "tri phú", "trung hà", "trung sơn", "trung thịnh", "trường sinh", "tùng vài",
    "vị xuyên", "việt lâm", "vĩnh tuy", "xín mần", "xuân giang", "xuân vân", "yên cường", "yên hoa",
    "yên lập", "yên minh", "yên nguyên", "yên phú", "yên thành"
]

OFFICIAL_WARD_NAMES = [
    "Phường Mỹ Lâm", "Phường Minh Xuân", "Phường Nông Tiến", "Phường An Tường", "Phường Bình Thuận",
    "Phường Hà Giang 1", "Phường Hà Giang 2",
    "Xã Thượng Lâm", "Xã Lâm Bình", "Xã Minh Quang", "Xã Bình An", "Xã Côn Lôn", "Xã Yên Hoa",
    "Xã Thượng Nông", "Xã Hồng Thái", "Xã Nà Hang", "Xã Tân Mỹ", "Xã Yên Lập", "Xã Tân An",
    "Xã Chiêm Hóa", "Xã Hòa An", "Xã Kiên Đài", "Xã Tri Phú", "Xã Kim Bình", "Xã Yên Nguyên",
    "Xã Yên Phú", "Xã Bạch Xa", "Xã Phù Lưu", "Xã Hàm Yên", "Xã Bình Xa", "Xã Thái Sơn",
    "Xã Thái Hòa", "Xã Hùng Lợi", "Xã Trung Sơn", "Xã Thái Bình", "Xã Tân Long", "Xã Xuân Vân",
    "Xã Lực Hành", "Xã Yên Sơn", "Xã Nhữ Khê", "Xã Tân Trào", "Xã Minh Thanh", "Xã Sơn Dương",
    "Xã Bình Ca", "Xã Tân Thanh", "Xã Sơn Thủy", "Xã Phú Lương", "Xã Trường Sinh", "Xã Hồng Sơn",
    "Xã Đông Thọ",
    "Xã Lũng Cú", "Xã Đồng Văn", "Xã Sà Phìn", "Xã Phố Bảng", "Xã Lũng Phìn", "Xã Sủng Máng",
    "Xã Sơn Vĩ", "Xã Mèo Vạc", "Xã Khâu Vai", "Xã Niêm Sơn", "Xã Tát Ngà", "Xã Thắng Mố",
    "Xã Bạch Đích", "Xã Yên Minh", "Xã Mậu Duệ", "Xã Du Già", "Xã Đường Thượng", "Xã Lùng Tám",
    "Xã Cán Tỷ", "Xã Nghĩa Thuận", "Xã Quản Bạ", "Xã Tùng Vài", "Xã Yên Cường", "Xã Đường Hồng",
    "Xã Bắc Mê", "Xã Minh Ngọc", "Xã Ngọc Đường", "Xã Lao Chải", "Xã Thanh Thủy", "Xã Phú Linh",
    "Xã Linh Hồ", "Xã Bạch Ngọc", "Xã Vị Xuyên", "Xã Việt Lâm", "Xã Tân Quang", "Xã Đồng Tâm",
    "Xã Liên Hiệp", "Xã Bằng Hành", "Xã Bắc Quang", "Xã Hùng An", "Xã Vĩnh Tuy", "Xã Đồng Yên",
    "Xã Tiên Yên", "Xã Xuân Giang", "Xã Bằng Lang", "Xã Yên Thành", "Xã Quang Bình", "Xã Tân Trịnh",
    "Xã Thông Nguyên", "Xã Hồ Thầu", "Xã Nậm Dịch", "Xã Tân Tiến", "Xã Hoàng Su Phì", "Xã Thàng Tín",
    "Xã Bản Máy", "Xã Pờ Ly Ngài", "Xã Xín Mần", "Xã Pà Vầy Sủ", "Xã Nấm Dẩn", "Xã Trung Thịnh",
    "Xã Khuôn Lùng", "Xã Trung Hà", "Xã Kiến Thiết", "Xã Hùng Đức", "Xã Minh Sơn", "Xã Minh Tân",
    "Xã Thuận Hòa", "Xã Tùng Bá", "Xã Thượng Sơn", "Xã Cao Bồ", "Xã Ngọc Long", "Xã Giáp Trung",
    "Xã Tiên Nguyên", "Xã Quảng Nguyên",
]
OFFICIAL_WARD_NAMES_LOWER = [w.lower() for w in OFFICIAL_WARD_NAMES]

# Tỉnh/thành khác (34 tỉnh mới + tên tỉnh cũ còn hay dùng). Bỏ "thái bình", "bình thuận",
# "hà giang" vì trùng tên xã/phường hoặc chính là địa bàn của Tuyên Quang.
OTHER_PROVINCE_SIGNALS = [
    "hà nội", "hồ chí minh", "tp.hcm", "tphcm", "hải phòng", "đà nẵng", "huế", "lai châu",
    "điện biên", "sơn la", "lào cai", "cao bằng", "lạng sơn", "thái nguyên", "phú thọ",
    "bắc ninh", "hưng yên", "quảng ninh", "ninh bình", "thanh hóa", "nghệ an", "hà tĩnh",
    "quảng trị", "quảng ngãi", "gia lai", "khánh hòa", "lâm đồng", "đắk lắk", "đăk lăk",
    "đồng nai", "tây ninh", "cần thơ", "vĩnh long", "đồng tháp", "cà mau", "an giang",
    # tên tỉnh cũ trước sáp nhập
    "yên bái", "bắc giang", "bắc kạn", "hải dương", "nam định", "hà nam", "vĩnh phúc",
    "hòa bình", "quảng bình", "quảng nam", "kon tum", "đắk nông", "đăk nông", "phú yên",
    "bình định", "ninh thuận", "bình phước", "bình dương", "long an", "tiền giang",
    "bến tre", "trà vinh", "sóc trăng", "hậu giang", "bạc liêu", "kiên giang",
    "bà rịa", "vũng tàu",
]


def _bo_dau(s):
    s = unicodedata.normalize("NFD", s.lower()).replace("đ", "d")
    return "".join(c for c in s if unicodedata.category(c) != "Mn")


def _regex_tu(ds):
    """Khớp nguyên cụm từ (tránh 'huế' khớp nhầm trong 'thuế')."""
    return re.compile(r"(?<!\w)(?:" + "|".join(re.escape(x) for x in ds) + r")(?!\w)")


RE_TINH_KHAC = _regex_tu(OTHER_PROVINCE_SIGNALS)
RE_XA_PHUONG = _regex_tu(OFFICIAL_WARD_NAMES_LOWER)
# Dạng không dấu, viết liền để dò trong tên miền/tên nguồn (vd daklak.gov.vn, baolaocai.vn)
SLUG_TINH_KHAC = sorted({_bo_dau(p).replace(" ", "").replace(".", "") for p in OTHER_PROVINCE_SIGNALS
                         if len(_bo_dau(p).replace(" ", "")) >= 5})
SLUG_TINH_NHA = ("tuyenquang", "hagiang")


# Nguồn bị chặn hẳn (mọi mục). Lâm Đồng có xã Tuyên Quang trùng tên tỉnh nên tin của họ hay
# lọt vào. Viết không dấu, không cách; dò trong tên nguồn + tên miền (vd baolamdong.vn,
# congan.lamdong.gov.vn, "Báo Lâm Đồng", "Công an tỉnh Lâm Đồng"). Muốn chặn thêm thì thêm vào đây.
NGUON_CHAN = ["lamdong"]


def nguon_bi_chan(nguon="", link=""):
    m = re.match(r"https?://([^/]+)", link or "")
    mien = m.group(1) if m and "news.google." not in m.group(1) else ""
    chuoi = _bo_dau((nguon or "") + " " + mien).replace(" ", "")
    return any(x in chuoi for x in NGUON_CHAN)


def nguon_tinh_khac(nguon="", link=""):
    """Tên nguồn hoặc tên miền là của tỉnh khác (vd 'Báo Lào Cai', 'daklak.gov.vn')."""
    if RE_TINH_KHAC.search((nguon or "").lower()):
        return True
    m = re.match(r"https?://([^/]+)", link or "")
    chuoi = _bo_dau((nguon or "") + " " + (m.group(1) if m and "news.google." not in m.group(1) else ""))
    chuoi = chuoi.replace(" ", "")
    if any(x in chuoi for x in SLUG_TINH_NHA):
        return False
    return any(x in chuoi for x in SLUG_TINH_KHAC)


# =====================================================================
# PHÂN LOẠI SẮC THÁI (bản 2)
# ---------------------------------------------------------------------
# Nguyên tắc: chấm theo TÁC ĐỘNG của tin đến hình ảnh địa phương, chính quyền,
# không chấm theo việc tin có xuất hiện từ ngữ về tội phạm hay không.
#   - Tiêu đề tính gấp đôi tóm tắt (tiêu đề nói rõ ý chính của bài).
#   - Khớp nguyên cụm từ, chuẩn hóa Unicode (tránh 'ngập' trong 'ngập tràn niềm vui').
#   - Từ ngữ pháp luật/tội phạm (vi phạm, ma túy, bị cáo, khởi tố...) KHÔNG bị tính
#     tiêu cực khi bài nói về hoạt động tuyên truyền, phòng ngừa, đấu tranh, triệt phá...
#     (vd phiên tòa giả định, tuyên truyền pháp luật, Công an triệt phá đường dây ma túy).
# Muốn chỉnh: thêm/bớt cụm từ ở 4 bảng dưới, con số là trọng số.
# =====================================================================

# ---- 3 NHÓM TỪ TIÊU CỰC ----
# Dân sinh, quản lý: luôn tính (loại tin dễ gây bức xúc dư luận)
NEG_DAN_SINH = {
    "bức xúc": 2, "kêu cứu": 2, "sai phạm": 2, "ô nhiễm": 2, "gây phẫn nộ": 2, "phẫn nộ": 2,
    "nợ lương": 2, "ăn chặn": 2, "nhũng nhiễu": 2, "hách dịch": 2, "thất thoát": 2,
    "chưa được giải quyết": 2, "chưa được xử lý": 2, "chưa được bồi thường": 2,
    "chưa được khắc phục": 2, "chưa được hỗ trợ": 2, "quá tải": 1,
    "hôi thối": 2, "ruồi nhặng": 1, "bủa vây": 1, "nứt nẻ": 1, "lầy lội": 1, "mất nước": 1,
    "mất điện": 1, "thiếu nước": 1, "kêu trời": 2, "khốn khổ": 2,
    "phản ánh": 1, "xuống cấp": 1, "chậm tiến độ": 1, "bất cập": 1, "lãng phí": 1,
    "khiếu kiện": 1, "tố cáo": 1, "đình trệ": 1,
}

# Thương vong: chỉ được bỏ qua khi bài là diễn tập/giả định
NEG_THUONG_VONG = {"tử vong": 2, "thiệt mạng": 2, "mất tích": 2, "thương vong": 2}

# Thiên tai, sự cố: bỏ qua khi TIÊU ĐỀ nói về ứng phó, phòng chống, cứu hộ, khắc phục
NEG_SU_CO = {
    "sạt lở": 1, "lũ quét": 1, "lũ ống": 1, "lũ lụt": 1, "mưa lũ": 1, "ngập úng": 1,
    "ngập lụt": 1, "bị ngập": 1, "ngập sâu": 1, "thiên tai": 1, "thiệt hại": 1,
    "tai nạn": 1, "mất an toàn": 1, "cháy rừng": 1, "hỏa hoạn": 1, "cháy nổ": 1,
    "sự cố": 1, "dông lốc": 1, "mưa đá": 1, "rét đậm": 1, "rét hại": 1,
    "đuối nước": 1, "bị thương": 1, "điện giật": 1,
}

# Pháp luật, tội phạm: bỏ qua khi TIÊU ĐỀ nói về tuyên truyền, đấu tranh, kiểm sát, triệt phá
NEG_PHAP_LUAT = {
    "lừa đảo": 2, "chiếm đoạt": 2, "khởi tố": 2, "giết người": 2, "tham nhũng": 2,
    "tham ô": 2, "hối lộ": 2,
    "vi phạm": 1, "tệ nạn": 1, "bắt giữ": 1, "bắt tạm giam": 1, "truy tố": 1, "xét xử": 1,
    "bị cáo": 1, "tội phạm": 1, "ma túy": 1, "đánh bạc": 1, "trộm cắp": 1,
    "cố ý gây thương tích": 1, "buôn lậu": 1, "gian lận": 1, "vụ án": 1,
}

# ---- 3 NHÓM NGỮ CẢNH (mỗi nhóm có ngữ cảnh: +2 điểm và bỏ qua nhóm từ tiêu cực tương ứng) ----
# Diễn tập, giả định: tình huống không có thật -> bỏ qua TẤT CẢ từ tiêu cực.
# Xét cả tiêu đề lẫn sapo (sapo bài diễn tập hay viết "giả định mưa lớn gây sạt lở...").
NGU_CANH_GIA_DINH = [
    "diễn tập", "giả định", "phiên tòa giả định", "tình huống giả định", "thực binh",
]
# Ứng phó, phòng chống thiên tai: chỉ xét TIÊU ĐỀ (tránh tin thiên tai thật bị tính tích cực
# chỉ vì sapo có câu "lực lượng chức năng đang ứng phó")
NGU_CANH_UNG_PHO = [
    "ứng phó", "phòng thủ dân sự", "phòng, chống thiên tai", "phòng chống thiên tai",
    "phòng, chống lụt bão", "phòng chống lụt bão", "cứu hộ", "cứu nạn", "tìm kiếm cứu nạn",
    "khắc phục hậu quả", "sơ tán", "di dời dân", "chủ động phòng", "sẵn sàng", "hỗ trợ người dân",
    "giúp dân", "phòng cháy", "chữa cháy", "pccc",
    # phòng ngừa tai nạn, sự cố (vd "Điện lực tăng cường phòng tránh tai nạn điện, cháy nổ")
    "phòng tránh", "phòng ngừa", "phòng, chống", "phòng chống", "ngăn ngừa", "ngăn chặn",
    "bảo vệ an toàn", "bảo đảm an toàn", "đảm bảo an toàn", "an toàn lưới điện",
    "an toàn giao thông", "an toàn lao động", "tuyên truyền", "tập huấn", "ra quân", "kiểm tra an toàn",
]
# Tuyên truyền, đấu tranh pháp luật: chỉ xét TIÊU ĐỀ (tránh "Khởi tố đối tượng lừa đảo"
# bị tính tích cực chỉ vì sapo có chữ "đấu tranh")
NGU_CANH_DAU_TRANH = [
    "tuyên truyền", "phổ biến pháp luật", "phổ biến, giáo dục pháp luật", "giáo dục pháp luật",
    "trợ giúp pháp lý", "phòng ngừa", "phòng, chống", "phòng chống", "ngăn chặn", "đấu tranh",
    "triệt phá", "ra quân", "tập huấn", "hội thi", "cao điểm", "kiểm sát", "truy bắt thành công",
]
# Chính quyền tiếp thu, xử lý phản ánh: chỉ xét TIÊU ĐỀ -> bỏ qua từ tiêu cực dân sinh
# (vd "Tuyên Quang tiếp thu, khắc phục ô nhiễm tại bãi rác"). Cụm phủ định như
# "chưa được khắc phục", "không giải quyết" bị loại trước khi dò nên không bị tính nhầm.
NGU_CANH_TIEP_THU = [
    "tiếp thu", "khắc phục", "xử lý dứt điểm", "giải quyết", "vào cuộc", "chấn chỉnh",
    "làm rõ", "trả lời", "đối thoại", "tháo gỡ", "chỉ đạo", "kiểm tra, xử lý", "khẩn trương xử lý",
    "di dời", "cải tạo", "nâng cấp", "sửa chữa",
]
# Xây dựng pháp luật, nghị trường: chỉ xét TIÊU ĐỀ -> bỏ qua từ pháp luật
# (vd "Đại biểu Quốc hội thảo luận về Luật Xử lý vi phạm hành chính")
NGU_CANH_LAP_PHAP = [
    "dự thảo", "dự án luật", "luật", "bộ luật", "nghị định", "thông tư", "nghị quyết",
    "thảo luận", "góp ý", "quốc hội", "đại biểu quốc hội", "kỳ họp", "hội đồng nhân dân", "hđnd",
    "tiếp xúc cử tri", "xử lý vi phạm hành chính",
]
# Tin dịch vụ, tiện ích (thời tiết, lịch cắt điện...): chỉ xét TIÊU ĐỀ -> bỏ qua từ thiên tai
# và dân sinh, KHÔNG cộng điểm (để ra Trung lập)
NGU_CANH_TIEN_ICH = [
    "thời tiết", "dự báo thời tiết", "lịch cắt điện", "lịch mất điện", "lịch cúp điện",
    "lịch tạm ngừng cấp điện", "xổ số", "giá vàng", "giá xăng",
    "cảnh báo", "khuyến cáo",   # tin cảnh báo, khuyến cáo -> Trung lập
]
DIEM_NGU_CANH = 2

POS_WORDS = {
    "biểu dương": 2, "khen thưởng": 2, "tuyên dương": 2, "vượt mức": 2, "vượt kế hoạch": 2,
    "khánh thành": 2, "đạt giải": 2, "giải nhất": 2,
    "hoàn thành": 1, "nông thôn mới": 1, "khang trang": 1, "hiệu quả": 1, "ủng hộ": 1,
    "đóng góp": 1, "khắc phục": 1, "phát triển": 1, "thành công": 1, "tăng trưởng": 1,
    "tăng tốc": 1, "khởi công": 1, "trao tặng": 1, "tặng quà": 1, "hỗ trợ": 1,
    "chúc mừng": 1, "tri ân": 1, "kỷ niệm": 1, "thăm hỏi": 1, "quảng bá": 1, "đón nhận": 1,
    "chủ động": 1, "nâng cao": 1, "thúc đẩy": 1, "khai mạc": 1, "lễ hội": 1, "ra mắt": 1,
    "tôn vinh": 1, "lan tỏa": 1, "tiếp thu": 1,
}


def _chuan_hoa(text):
    """NFC + chữ thường + gộp khoảng trắng (một số báo dùng Unicode tổ hợp làm khớp trượt)."""
    return " ".join(unicodedata.normalize("NFC", text or "").lower().split())


def _bo_khop(bang):
    tu = sorted(bang, key=len, reverse=True)  # cụm dài khớp trước
    return re.compile(r"(?<!\w)(" + "|".join(re.escape(x) for x in tu) + r")(?!\w)")


RE_POS = _bo_khop(POS_WORDS)
NHOM_TIEU_CUC = [  # (tên nhóm, bảng từ, regex)
    ("dan_sinh", NEG_DAN_SINH, _bo_khop(NEG_DAN_SINH)),
    ("su_co", NEG_SU_CO, _bo_khop(NEG_SU_CO)),
    ("phap_luat", NEG_PHAP_LUAT, _bo_khop(NEG_PHAP_LUAT)),
    ("thuong_vong", NEG_THUONG_VONG, _bo_khop(NEG_THUONG_VONG)),
]
RE_TIEP_THU = _bo_khop(NGU_CANH_TIEP_THU)
RE_LAP_PHAP = _bo_khop(NGU_CANH_LAP_PHAP)
RE_TIEN_ICH = _bo_khop(NGU_CANH_TIEN_ICH)
# "chưa được khắc phục", "không giải quyết", "chưa hề xử lý"... -> bỏ khi dò từ tích cực/ngữ cảnh
RE_PHU_DINH = re.compile(r"(?<!\w)(?:chưa|không|chẳng)(?:\s+(?:được|hề|có|kịp|thể))*\s+\S+(?:\s+\S+)?")
RE_GIA_DINH = _bo_khop(NGU_CANH_GIA_DINH)
RE_UNG_PHO = _bo_khop(NGU_CANH_UNG_PHO)
RE_DAU_TRANH = _bo_khop(NGU_CANH_DAU_TRANH)


def _tim(regex, text):
    return {m.group(1) for m in regex.finditer(text)}


def _diem_doan(text, bo_qua):
    """Trả về (điểm tích cực, điểm tiêu cực, cụm đã khớp); bo_qua = tập nhóm tiêu cực được bỏ qua."""
    pos = neg = 0
    khop = []
    for m in RE_POS.finditer(RE_PHU_DINH.sub(" ", text)):
        pos += POS_WORDS[m.group(1)]
        khop.append("+" + m.group(1))
    for ten, bang, rx in NHOM_TIEU_CUC:
        if ten in bo_qua:
            continue
        for m in rx.finditer(text):
            neg += bang[m.group(1)]
            khop.append("-" + m.group(1))
    return pos, neg, khop


def phan_tich_sac_thai(tieu_de, tom_tat=""):
    """Trả về dict: nhan (Tích cực/Trung lập/Tiêu cực), diem, ngu_canh, khop (để dò lỗi)."""
    td, tt = _chuan_hoa(tieu_de), _chuan_hoa(tom_tat)
    td_kd = RE_PHU_DINH.sub(" ", td)   # tiêu đề đã bỏ cụm phủ định, dùng để dò ngữ cảnh
    nc_gia_dinh = _tim(RE_GIA_DINH, td + " | " + tt)
    nc_ung_pho = _tim(RE_UNG_PHO, td_kd)
    nc_dau_tranh = _tim(RE_DAU_TRANH, td_kd) | _tim(RE_LAP_PHAP, td_kd)
    nc_tiep_thu = _tim(RE_TIEP_THU, td_kd)
    nc_tien_ich = _tim(RE_TIEN_ICH, td)

    bo_qua = set()
    if nc_gia_dinh:
        bo_qua |= {"dan_sinh", "su_co", "phap_luat", "thuong_vong"}
    if nc_ung_pho:
        bo_qua.add("su_co")
    if nc_dau_tranh:
        bo_qua.add("phap_luat")
    if nc_tiep_thu:
        bo_qua.add("dan_sinh")
    if nc_tien_ich:
        bo_qua |= {"dan_sinh", "su_co"}

    # Tiêu đề là bài phòng ngừa/tuyên truyền/xử lý -> số liệu thương vong nêu trong SAPO chỉ là
    # dẫn chứng (vd "năm qua có 5 em tử vong vì đuối nước"), không tính. Thương vong ở TIÊU ĐỀ vẫn tính.
    bo_qua_sapo = set(bo_qua)
    if nc_ung_pho or nc_dau_tranh or nc_tiep_thu:
        bo_qua_sapo.add("thuong_vong")

    p1, n1, k1 = _diem_doan(td, bo_qua)
    p2, n2, k2 = _diem_doan(tt, bo_qua_sapo)
    nc_cong_diem = nc_gia_dinh | nc_ung_pho | nc_dau_tranh | nc_tiep_thu
    ngu_canh = sorted(nc_cong_diem | nc_tien_ich)
    diem = 2 * (p1 - n1) + (p2 - n2) + (DIEM_NGU_CANH if nc_cong_diem else 0)
    nhan = "Tiêu cực" if diem < 0 else "Tích cực" if diem > 0 else "Trung lập"
    return {"nhan": nhan, "diem": diem, "ngu_canh": ngu_canh,
            "khop_tieu_de": k1, "khop_tom_tat": k2}


def analyze_sentiment(tieu_de, tom_tat=""):
    return phan_tich_sac_thai(tieu_de, tom_tat)["nhan"]


# =====================================================================
# HÀM TIỆN ÍCH (giữ logic bản v5.7)
# =====================================================================
def gnews_query_url(query, when="3d"):
    return f"https://news.google.com/rss/search?q={quote(query)}+when:{when}&hl=vi&gl=VN&ceid=VN:vi"


def build_ward_group_queries(group_size=10):
    skip = {"hà giang 1", "hà giang 2", "na hang"}
    wards = [w.title() for w in LOCAL_KEYWORDS if w not in skip]
    queries = []
    for i in range(0, len(wards), group_size):
        chunk = wards[i:i + group_size]
        queries.append("(" + " OR ".join(f'"{w}"' for w in chunk) + ")")
    return queries


# "xã Tuyên Quang", "đường Tuyên Quang"... là địa danh TRÙNG TÊN ở tỉnh khác (vd xã Tuyên Quang
# thuộc Lâm Đồng, đường Tuyên Quang ở Phan Thiết, Hà Nội...), không phải tỉnh mình.
# Giữ nguyên "phường Hà Giang 1/2" (của tỉnh mình) và tên tuyến "đường Tuyên Quang - Hà Giang"
# (có dấu gạch nối phía sau).
RE_DIA_DANH_TRUNG_TEN = re.compile(
    r"(?<!\w)(?:xã|phường|thị trấn|thôn|bản|xóm|làng|tổ dân phố|ấp|khu phố"
    r"|đường|phố|ngõ|ngách|hẻm|kiệt|con đường|tuyến phố)\s+"
    r"(?:tuyên quang|hà giang(?!\s*\d))(?!\w)(?!\s*[-–—])")


def _bo_dia_danh_trung(text):
    t = unicodedata.normalize("NFC", text or "").lower()
    return RE_DIA_DANH_TRUNG_TEN.sub(" ", t)


def nhac_tinh_nha(text):
    """Có nhắc đến TỈNH Tuyên Quang (hoặc Hà Giang cũ), không tính 'xã Tuyên Quang' của tỉnh khác."""
    t = _bo_dia_danh_trung(text)
    return "tuyên quang" in t or "hà giang" in t


def nhac_tuyen_quang(text):
    return nhac_tinh_nha(text)


def is_local_content(title, summary, nguon="", link=""):
    """
    - Nhắc rõ tỉnh "Tuyên Quang" -> liên quan ("xã Tuyên Quang", "Công an xã Tuyên Quang"
      là xã trùng tên ở tỉnh Lâm Đồng nên KHÔNG tính).
    - Chỉ khớp tên xã/phường -> phải KHÔNG nhắc tỉnh khác, và nguồn/tên miền KHÔNG phải
      của tỉnh khác (vd 'xã Tân Tiến' trên daklak.gov.vn là của Đắk Lắk).
      Sau khi bóc được bài, script còn kiểm tra lại toàn văn (xem xu_ly_mot_bai).
    """
    content = _bo_dia_danh_trung(title + " " + summary)
    if "tuyên quang" in content:
        return True
    # "Hà Giang" (tỉnh cũ, nay thuộc Tuyên Quang) -> liên quan, trừ khi nhắc tỉnh khác/nguồn tỉnh khác
    if re.search(r"(?<!\w)hà giang(?!\w)", content) and not RE_TINH_KHAC.search(content) \
            and not nguon_tinh_khac(nguon, link):
        return True
    if not RE_XA_PHUONG.search(content):
        return False
    if RE_TINH_KHAC.search(content):
        return False
    return not nguon_tinh_khac(nguon, link)


def is_safe(title, link, summary):
    content = (title + " " + link + " " + summary).lower()
    return not any(bad in content for bad in BLACKLIST)


def clean_html(raw_html):
    if not raw_html:
        return ""
    return " ".join(re.sub(r"<.*?>", "", raw_html).split())


def title_key(title):
    return re.sub(r"\W+", "", title.lower())[:80]


def make_khoa(title):
    return hashlib.sha1(title_key(title).encode("utf-8")).hexdigest()[:16]


# =====================================================================
# CẤU HÌNH 5 MỤC TIN
# =====================================================================
MUC = {
    "tieudiem": {
        "feeds": ["https://news.google.com/news/rss/headlines/section/topic/NATION?hl=vi&gl=VN&ceid=VN%3Avi"],
        "local": False, "cap": 50,
    },
    "quocte": {
        "feeds": ["https://www.vietnamplus.vn/rss/thegioi.rss"],
        "local": False, "cap": 50,
    },
    "mxh": {
        "feeds": [
            gnews_query_url('("facebook" OR "fanpage" OR "mạng xã hội" OR "tiktok") "Tuyên Quang"', when="2d"),
            gnews_query_url('("dư luận" OR "phản ánh" OR "bức xúc") "Tuyên Quang"', when="2d"),
            gnews_query_url('"Tuyên Quang"', when="1d"),
        ],
        "local": True, "cap": 80,
    },
    "diaphuong": {
        "feeds": [gnews_query_url('"Tuyên Quang"', when="14d")]
                 + [gnews_query_url(q, when="14d") for q in build_ward_group_queries(10)],
        "local": True, "cap": 200,
    },
    "tuyengiao": {
        "feeds": ["https://news.google.com/rss/search?q=(site:dangcongsan.vn+OR+site:tuyengiaodanvan.vn+OR+site:nhandan.vn)+(%22Ban+Tuy%C3%AAn+gi%C3%A1o%22+OR+%22D%C3%A2n+v%E1%BA%ADn%22)+when:3d&hl=vi&gl=VN&ceid=VN:vi"],
        "local": False, "cap": 50,
    },
}

http = requests.Session()
http.headers.update({"User-Agent": UA, "Accept-Language": "vi-VN,vi;q=0.9,en;q=0.6"})


# =====================================================================
# BƯỚC 1: QUÉT RSS
# =====================================================================
def doc_rss(url):
    for lan in range(3):
        try:
            r = http.get(url, timeout=25)
            if r.status_code == 200:
                return feedparser.parse(r.content).entries
            print(f"  ! RSS {r.status_code}: {url[:90]}")
        except Exception as ex:
            print(f"  ! Lỗi RSS ({ex.__class__.__name__}): {url[:90]}")
        time.sleep(2 + lan * 3)
    return []


def tach_entry(e):
    """Chuẩn hóa 1 entry RSS -> dict. Bỏ đuôi ' - Tên báo' mà Google News gắn vào tiêu đề."""
    title = (e.get("title") or "").strip()
    link = e.get("link") or ""
    summary = clean_html(e.get("summary", ""))
    nguon = ""
    src = e.get("source")
    if src and isinstance(src, dict):
        nguon = (src.get("title") or "").strip()
    if nguon and title.endswith(" - " + nguon):
        title = title[: -len(" - " + nguon)].strip()
    if not nguon:
        m = re.match(r"https?://(?:www\.)?([^/]+)", link)
        nguon = m.group(1) if m and "news.google." not in m.group(1) else ""
    ts = None
    if e.get("published_parsed"):
        try:
            ts = dt.datetime.fromtimestamp(calendar.timegm(e["published_parsed"]), tz=dt.timezone.utc)
        except Exception:
            ts = None
    # tóm tắt RSS của Google News chỉ lặp lại tiêu đề -> bỏ
    if summary.startswith(title[:40]):
        summary = ""
    return {"title": title, "link": link, "summary": summary, "nguon": nguon, "ts": ts}


def quet_tat_ca():
    bai = {}  # khoa -> record
    for ma_muc, cfg in MUC.items():
        print(f"\n== Quét mục [{ma_muc}] ({len(cfg['feeds'])} nguồn)")
        seen, ds = set(), []
        for url in cfg["feeds"]:
            for e in doc_rss(url):
                it = tach_entry(e)
                if not it["title"] or not is_safe(it["title"], it["link"], it["summary"]):
                    continue
                if nguon_bi_chan(it["nguon"], it["link"]):
                    continue
                k = title_key(it["title"])
                if not k or k in seen:
                    continue
                if cfg["local"] and not is_local_content(it["title"], it["summary"], it["nguon"], it["link"]):
                    continue
                seen.add(k)
                ds.append(it)
            if "news.google.com" in url:
                time.sleep(1.2)  # tránh bị Google chặn khi gọi dồn
        ds.sort(key=lambda x: x["ts"].timestamp() if x["ts"] else 0, reverse=True)
        ds = ds[: cfg["cap"]]
        print(f"   -> {len(ds)} tin")
        for it in ds:
            khoa = make_khoa(it["title"])
            if khoa not in bai:
                bai[khoa] = {**it, "khoa": khoa, "muc": set()}
            bai[khoa]["muc"].add(ma_muc)
    return bai


# =====================================================================
# SUPABASE (REST)
# =====================================================================
def sb_headers(extra=None):
    h = {"apikey": SUPABASE_KEY, "Content-Type": "application/json"}
    if SUPABASE_KEY.startswith("eyJ"):  # khóa kiểu cũ (JWT); khóa mới sb_secret_... chỉ cần apikey
        h["Authorization"] = f"Bearer {SUPABASE_KEY}"
    if extra:
        h.update(extra)
    return h


def sb_lay_ban_ghi(khoas):
    """Lấy các bản ghi đã có theo danh sách khóa."""
    co_san = {}
    khoas = list(khoas)
    for i in range(0, len(khoas), 100):
        chunk = khoas[i:i + 100]
        r = requests.get(
            f"{SUPABASE_URL}/rest/v1/dt_bai",
            params={"select": "khoa,muc,trang_thai,so_lan_thu,link_goc", "khoa": f"in.({','.join(chunk)})"},
            headers=sb_headers(), timeout=30)
        r.raise_for_status()
        for row in r.json():
            co_san[row["khoa"]] = row
    return co_san


def sb_upsert(rows):
    for i in range(0, len(rows), 200):
        r = requests.post(
            f"{SUPABASE_URL}/rest/v1/dt_bai", params={"on_conflict": "khoa"},
            headers=sb_headers({"Prefer": "resolution=merge-duplicates,return=minimal"}),
            data=json.dumps(rows[i:i + 200], ensure_ascii=False).encode("utf-8"), timeout=60)
        if r.status_code >= 300:
            print("  ! Lỗi upsert:", r.status_code, r.text[:300])
            r.raise_for_status()


def sb_cap_nhat(khoa, data):
    r = requests.patch(
        f"{SUPABASE_URL}/rest/v1/dt_bai", params={"khoa": f"eq.{khoa}"},
        headers=sb_headers({"Prefer": "return=minimal"}),
        data=json.dumps(data, ensure_ascii=False).encode("utf-8"), timeout=30)
    if r.status_code >= 300:
        print("  ! Lỗi cập nhật", khoa, r.status_code, r.text[:200])


def sb_cham_lai_sac_thai():
    """
    Rà lại tin gần đây (chỉ ghi những tin có thay đổi):
      - chấm lại sắc thái theo bộ từ điển hiện tại;
      - tin mục Địa phương/MXH không còn qua bộ lọc địa bàn -> đánh dấu ngoai_tinh để ẩn
        (vd tin "Công an xã Tuyên Quang" của Lâm Đồng đã lọt vào trước khi sửa bộ lọc).
    """
    moc = (dt.datetime.now(dt.timezone.utc) - dt.timedelta(days=SO_NGAY_CHAM_LAI)).isoformat()
    # Supabase chỉ trả tối đa 1000 dòng mỗi lần -> lấy theo từng trang, tin mới nhất trước
    rows, trang = [], 1000
    try:
        while True:
            r = requests.get(
                f"{SUPABASE_URL}/rest/v1/dt_bai",
                params={"select": "khoa,tieu_de,tom_tat,cam_xuc,muc,nguon,link_goc,ngoai_tinh",
                        "thoi_gian": f"gte.{moc}", "order": "thoi_gian.desc,khoa.asc",
                        "limit": str(trang), "offset": str(len(rows))},
                headers=sb_headers(), timeout=60)
            r.raise_for_status()
            phan = r.json()
            rows.extend(phan)
            if len(phan) < trang or len(rows) >= 20000:
                break
    except Exception as ex:
        print("  ! Không lấy được tin để chấm lại:", ex)
        if not rows:
            return
    doi = an = 0
    for row in rows:
        cap_nhat = {}
        moi = analyze_sentiment(row.get("tieu_de") or "", row.get("tom_tat") or "")
        if moi != row.get("cam_xuc"):
            cap_nhat["cam_xuc"] = moi
            doi += 1
        if not row.get("ngoai_tinh") and (
                nguon_bi_chan(row.get("nguon") or "", row.get("link_goc") or "")
                or (set(row.get("muc") or []) & {"diaphuong", "mxh"}
                    and not is_local_content(row.get("tieu_de") or "", row.get("tom_tat") or "",
                                             row.get("nguon") or "", row.get("link_goc") or ""))):
            cap_nhat["ngoai_tinh"] = True
            an += 1
        if cap_nhat:
            sb_cap_nhat(row["khoa"], cap_nhat)
    print(f"Rà lại {len(rows)} tin trong {SO_NGAY_CHAM_LAI} ngày: đổi nhãn sắc thái {doi} tin, ẩn {an} tin ngoài tỉnh.")


def sb_xoa_tin_cu():
    moc = (dt.datetime.now(dt.timezone.utc) - dt.timedelta(days=SO_NGAY_LUU)).isoformat()
    r = requests.delete(
        f"{SUPABASE_URL}/rest/v1/dt_bai", params={"quet_luc": f"lt.{moc}"},
        headers=sb_headers({"Prefer": "return=minimal"}), timeout=30)
    print("Xóa tin cũ:", "OK" if r.status_code < 300 else f"lỗi {r.status_code} {r.text[:200]}")


# =====================================================================
# BƯỚC 3a: GIẢI MÃ LINK GOOGLE NEWS -> LINK BÁO GỐC
# =====================================================================
_khoa_google = threading.Lock()


def _giai_ma_base64_cu(gid):
    """Kiểu link cũ: link gốc nằm ngay trong chuỗi base64."""
    try:
        raw = base64.urlsafe_b64decode(gid + "=" * (-len(gid) % 4))
        m = re.search(rb"https?://[^\x00-\x20\x7f-\xff]+", raw)
        if m and b"AU_yqL" not in raw[:10]:
            return m.group(0).decode("ascii", "ignore")
    except Exception:
        pass
    return None


def _tach_ket_qua_batchexecute(text):
    """Phân tích phản hồi batchexecute của Google, trả về link gốc hoặc None."""
    try:
        phan = text.split("\n\n")[1]
        data = json.loads(phan)[:-2]
        return json.loads(data[0][2])[1]
    except Exception:
        m = re.search(r'\\"(https?://[^"\\]+)\\"', text)
        return m.group(1) if m else None


def giai_ma_google(url):
    m = re.search(r"news\.google\.com/(?:rss/)?(?:articles|read)/([A-Za-z0-9_\-]+)", url)
    if not m:
        return url
    gid = m.group(1)
    cu = _giai_ma_base64_cu(gid)
    if cu:
        return cu
    with _khoa_google:  # gọi tuần tự tới Google, tránh bị chặn
        try:
            r = http.get(f"https://news.google.com/rss/articles/{gid}", timeout=20)
            sig = re.search(r'data-n-a-sg="([^"]+)"', r.text)
            ts = re.search(r'data-n-a-ts="([^"]+)"', r.text)
            if not sig or not ts:
                r = http.get(f"https://news.google.com/articles/{gid}", timeout=20)
                sig = re.search(r'data-n-a-sg="([^"]+)"', r.text)
                ts = re.search(r'data-n-a-ts="([^"]+)"', r.text)
            if not sig or not ts:
                return None
            req = [
                "Fbv4je",
                f'["garturlreq",[["X","X",["X","X"],null,null,1,1,"US:en",null,1,null,null,null,null,null,0,1],'
                f'"X","X",1,[1,1,1],1,1,null,0,0,null,0],"{gid}",{ts.group(1)},"{sig.group(1)}"]',
            ]
            r2 = http.post(
                "https://news.google.com/_/DotsSplashUi/data/batchexecute",
                headers={"Content-Type": "application/x-www-form-urlencoded;charset=UTF-8"},
                data="f.req=" + quote(json.dumps([[req]])), timeout=20)
            return _tach_ket_qua_batchexecute(r2.text)
        except Exception as ex:
            print("  ! Giải mã Google lỗi:", ex.__class__.__name__)
            return None
        finally:
            time.sleep(0.6)


# =====================================================================
# BƯỚC 3b: TẢI BÀI & BÓC NỘI DUNG
# =====================================================================
def boc_noi_dung(link):
    r = http.get(link, timeout=25, allow_redirects=True)
    if r.status_code != 200:
        return None
    doc = trafilatura.bare_extraction(
        r.content, url=r.url, with_metadata=True, include_comments=False,
        include_tables=False, include_images=False, favor_precision=True,
        date_extraction_params={"extensive_search": True, "original_date": True,
                                "outputformat": "%Y-%m-%d"})
    if doc is None:
        return None
    if not isinstance(doc, dict):
        doc = doc.as_dict()
    text = (doc.get("text") or "").strip()
    # trafilatura trả các đoạn cách nhau bởi 1 dòng mới -> đổi sang dòng trống cho dễ hiển thị
    doan = cat_phan_thua([d.strip() for d in text.split("\n") if d.strip()])
    return {
        "noi_dung": "\n\n".join(doan),
        "tom_tat": (doc.get("description") or "").strip(),
        "anh": doc.get("image") or None,
        "link_cuoi": r.url,
        "ngay": doc.get("date"),
    }


VN_TZ = dt.timezone(dt.timedelta(hours=7))

# Một số báo (Bnews, VietnamPlus...) để danh sách "Tin liên quan / Tin cùng chuyên mục" ngay
# trong thân bài -> cắt bỏ từ đoạn tiêu đề đó trở đi, bỏ các đoạn chỉ có dấu gạch.
MOC_PHAN_THUA = {
    "tin liên quan", "tin cùng chuyên mục", "tin khác", "các tin khác", "xem thêm", "đọc thêm",
    "bài liên quan", "bài viết liên quan", "có thể bạn quan tâm", "tin mới nhất", "tin đọc nhiều",
    "tin nổi bật", "tin mới", "cùng chuyên mục", "tin tức liên quan",
}


def cat_phan_thua(doan):
    kq = []
    for i, d in enumerate(doan):
        chuan = _chuan_hoa(d).strip(" :.-–>»")
        if i >= 2 and chuan in MOC_PHAN_THUA:
            break
        if re.fullmatch(r"[\s\-–—_•·*|]+", d):
            continue
        kq.append(d)
    return kq


def ngay_dang_that(ngay_bai, ts_rss):
    """
    Google News ghi thời gian theo lúc Google thấy bài, nên bài cũ được đăng lại/được
    cập nhật vẫn hiện như tin mới. Nếu ngày đăng ghi TRÊN TRANG BÁO sớm hơn ngày trong RSS
    thì lấy ngày trên trang báo (tính 07:00 sáng giờ Việt Nam ngày đó).
    Trả về chuỗi ISO hoặc None nếu không cần sửa.
    """
    if not ngay_bai:
        return None
    try:
        d = dt.datetime.strptime(ngay_bai[:10], "%Y-%m-%d").replace(hour=7, tzinfo=VN_TZ)
    except ValueError:
        return None
    if d.year < 2000:
        return None
    if ts_rss is None:
        return d.isoformat()
    if d.date() < ts_rss.astimezone(VN_TZ).date():
        return d.isoformat()
    return None


def xu_ly_mot_bai(rec):
    khoa = rec["khoa"]
    link_goc = rec.get("link_goc")
    if not link_goc:
        link_goc = giai_ma_google(rec["link"]) if "news.google.com" in rec["link"] else rec["link"]
    cap_nhat = {"so_lan_thu": rec.get("so_lan_thu", 0) + 1}

    # Tin vào mục Địa phương/MXH chỉ nhờ trùng tên xã (tiêu đề không có chữ "Tuyên Quang")
    # -> cần kiểm tra thêm xem có đúng là tin của tỉnh mình không.
    can_xac_minh = (bool(rec["muc"] & {"diaphuong", "mxh"})
                    and "tuyên quang" not in _bo_dia_danh_trung(rec["title"] + " " + rec.get("summary", "")))

    if not link_goc:
        cap_nhat["trang_thai"] = "loi"
        sb_cap_nhat(khoa, cap_nhat)
        return khoa, "không giải mã được link"
    cap_nhat["link_goc"] = link_goc
    if nguon_bi_chan(rec.get("nguon", ""), link_goc):
        cap_nhat["ngoai_tinh"] = True
    if can_xac_minh and nguon_tinh_khac(rec.get("nguon", ""), link_goc):
        cap_nhat["ngoai_tinh"] = True

    try:
        kq = boc_noi_dung(link_goc)
    except Exception as ex:
        kq = None
        print("  ! Tải bài lỗi:", ex.__class__.__name__, link_goc[:80])

    if kq:
        ngay = ngay_dang_that(kq.get("ngay"), rec.get("ts"))
        if ngay:
            cap_nhat["thoi_gian"] = ngay
        if kq["tom_tat"]:
            cap_nhat["tom_tat"] = kq["tom_tat"][:600]
            cap_nhat["cam_xuc"] = analyze_sentiment(rec["title"], kq["tom_tat"])
        if can_xac_minh and nguon_tinh_khac("", kq["link_cuoi"] or ""):
            cap_nhat["ngoai_tinh"] = True

    if kq and len(kq["noi_dung"]) >= 200:
        cap_nhat.update({
            "noi_dung": kq["noi_dung"],
            "anh": kq["anh"],
            "trang_thai": "ok",
            "link_goc": kq["link_cuoi"] or link_goc,
        })
        # Toàn văn không hề nhắc Tuyên Quang/Hà Giang -> tin của xã trùng tên ở tỉnh khác
        if can_xac_minh and not nhac_tuyen_quang(kq["tom_tat"] + " " + kq["noi_dung"]):
            cap_nhat["ngoai_tinh"] = True
        sb_cap_nhat(khoa, cap_nhat)
        return khoa, "ok"

    cap_nhat["trang_thai"] = "loi"
    sb_cap_nhat(khoa, cap_nhat)
    return khoa, "không bóc được nội dung"


# =====================================================================
# CHẠY
# =====================================================================
def thu_sac_thai(tieu_de, tom_tat=""):
    kq = phan_tich_sac_thai(tieu_de, tom_tat)
    print(f"Nhãn      : {kq['nhan']}  (điểm {kq['diem']})")
    print(f"Ngữ cảnh  : {', '.join(kq['ngu_canh']) or '—'}")
    print(f"Tiêu đề   : {', '.join(kq['khop_tieu_de']) or '—'}  (x2)")
    print(f"Tóm tắt   : {', '.join(kq['khop_tom_tat']) or '—'}")


def main():
    if len(sys.argv) >= 3 and sys.argv[1] == "--thu-dia-ban":
        nguon = sys.argv[3] if len(sys.argv) > 3 else ""
        ok = not nguon_bi_chan(nguon, nguon) and is_local_content(sys.argv[2], "", nguon, "")
        print("Địa bàn:", "THUỘC Tuyên Quang -> giữ" if ok else "NGOÀI tỉnh -> loại")
        return
    if len(sys.argv) >= 3 and sys.argv[1] == "--thu":
        thu_sac_thai(sys.argv[2], sys.argv[3] if len(sys.argv) > 3 else "")
        return

    if not SUPABASE_URL or not SUPABASE_KEY:
        sys.exit("Thiếu SUPABASE_URL hoặc SUPABASE_SERVICE_KEY")

    t0 = time.time()
    print(f"== quet_tin.py phiên bản {PHIEN_BAN}")

    # Rà lại tin cũ TRƯỚC khi quét (bước này nhanh), để dù bước quét/bóc bài có lỗi
    # hay hết giờ thì nhãn sắc thái và bộ lọc địa bàn mới vẫn được áp dụng.
    try:
        sb_cham_lai_sac_thai()
    except Exception as ex:
        print("  ! Lỗi rà lại tin cũ:", ex)

    bai = quet_tat_ca()
    print(f"\nTổng cộng {len(bai)} tin khác nhau.")

    if bai:
        co_san = sb_lay_ban_ghi(bai.keys())
        now = dt.datetime.now(dt.timezone.utc).isoformat()

        moi, cu = [], []
        for khoa, rec in bai.items():
            old = co_san.get(khoa)
            if old:
                muc = sorted(set(old.get("muc") or []) | rec["muc"])
                cu.append({"khoa": khoa, "tieu_de": rec["title"], "muc": muc, "quet_luc": now})
                rec["link_goc"] = old.get("link_goc")
                rec["trang_thai"] = old.get("trang_thai")
                rec["so_lan_thu"] = old.get("so_lan_thu") or 0
            else:
                moi.append({
                    "khoa": khoa, "muc": sorted(rec["muc"]), "tieu_de": rec["title"], "nguon": rec["nguon"],
                    "link_rss": rec["link"], "tom_tat": rec["summary"] or None,
                    "cam_xuc": analyze_sentiment(rec["title"], rec["summary"]),
                    "thoi_gian": rec["ts"].isoformat() if rec["ts"] else now,
                    "quet_luc": now, "trang_thai": "cho", "so_lan_thu": 0,
                })
                rec["trang_thai"], rec["so_lan_thu"] = "cho", 0

        print(f"Tin mới: {len(moi)} · Tin đã có: {len(cu)}")
        if moi:
            sb_upsert(moi)
        if cu:
            sb_upsert(cu)

        # Bóc nội dung cho tin chưa có, ưu tiên tin mới nhất
        can_boc = [r for r in bai.values()
                   if r["trang_thai"] in ("cho", "loi") and r["so_lan_thu"] < SO_LAN_THU_TOI_DA]
        can_boc.sort(key=lambda x: x["ts"].timestamp() if x["ts"] else 0, reverse=True)
        can_boc = can_boc[:MAX_TRICH_XUAT]
        print(f"\nBóc nội dung {len(can_boc)} bài...")
        dem = {"ok": 0, "loi": 0}
        with ThreadPoolExecutor(max_workers=SO_LUONG) as pool:
            for f in as_completed([pool.submit(xu_ly_mot_bai, r) for r in can_boc]):
                try:
                    _, kq = f.result()
                    dem["ok" if kq == "ok" else "loi"] += 1
                except Exception as ex:
                    dem["loi"] += 1
                    print("  ! Lỗi xử lý:", ex)
        print(f"   -> bóc được {dem['ok']}, lỗi {dem['loi']}")

    try:
        sb_xoa_tin_cu()
    except Exception as ex:
        print("  ! Lỗi xóa tin cũ:", ex)
    print(f"\nXong sau {time.time() - t0:.0f} giây.")


if __name__ == "__main__":
    main()
